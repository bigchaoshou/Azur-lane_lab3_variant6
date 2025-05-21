import copy
import logging
from collections import namedtuple
import matplotlib.pyplot as plt
import re

ReductionEvent = namedtuple("ReductionEvent",
                           "clock term reduced_term rule")


class Term:
    def __init__(self, term_type, value=None, left=None, right=None):
        self.term_type = term_type  # 'VAR', 'LAM', 'APP'
        self.value = value          # Variable name or bound variable
        self.left = left            # Left subterm
        self.right = right          # Right subterm

        if self.term_type == 'LAM':
            assert right is not None, (
                f"LAM node with param {value} has no body")
        if self.term_type == 'APP':
            assert (left is not None and right is not None), (
                "APP node has None child")

    def __repr__(self):
        if self.term_type == 'VAR':
            return self.value
        elif self.term_type == 'LAM':
            return f"(λ{self.value}.{self.right})"
        elif self.term_type == 'APP':
            return f"({self.left} {self.right})"
        return ""


def tokenize(expr):
    tokens = re.findall(r'[λ\\]|[a-zA-Z_]\w*|\(|\)|\.', expr)
    return tokens


class LambdaParser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def current(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def eat(self, expected=None):
        tok = self.current()
        if expected and tok != expected:
            raise SyntaxError(f"Expected {expected} but got {tok}")
        self.pos += 1
        return tok

    def parse(self):
        return self.parse_expr()

    def parse_expr(self):
        term = self.parse_atom()
        while True:
            next_tok = self.current()
            if next_tok and next_tok not in [')', '.']:
                term = Term('APP', left=term, right=self.parse_atom())
            else:
                break
        return term

    def parse_atom(self):
        tok = self.current()
        if tok in ['λ', '\\']:
            self.eat()
            var = self.eat()
            self.eat('.')
            body = self.parse_expr()
            return Term('LAM', var, right=body)
        elif tok == '(':
            self.eat('(')
            expr = self.parse_expr()
            self.eat(')')
            return expr
        elif re.match(r'[a-zA-Z_]\w*', tok):
            return Term('VAR', self.eat())
        else:
            raise SyntaxError(f"Unexpected token: {tok}")


def parse_lambda_expr(expr_str):
    tokens = tokenize(expr_str)
    parser = LambdaParser(tokens)
    return parser.parse()


class LambdaInterpreter:
    def __init__(self, strategy="normal", enable_eta=True):
        self.strategy = strategy
        self.enable_eta = enable_eta
        self.event_history = []
        self.counter = 0
        logging.basicConfig(level=logging.DEBUG, format='%(message)s')
        self.logger = logging.getLogger("LambdaInterpreter")
        self.indent_level = 0

    def _log(self, msg):
        indent = "  " * self.indent_level
        self.logger.debug(indent + msg)

    def fresh_var(self, base='x'):
        self.counter += 1
        return f"{base}_{self.counter}"

    def free_vars(self, term):
        if term is None:
            return set()
        if term.term_type == 'VAR':
            return {term.value}
        elif term.term_type == 'LAM':
            return self.free_vars(term.right) - {term.value}
        elif term.term_type == 'APP':
            return (self.free_vars(term.left)
                    | self.free_vars(term.right))
        return set()

    def alpha_convert(self, term, old_var, new_var):
        if term is None:
            return None
        if term.term_type == 'VAR':
            return (Term('VAR', new_var)
                    if term.value == old_var else term)
        elif term.term_type == 'LAM':
            if term.value == old_var:
                return Term('LAM', new_var,
                            right=self.alpha_convert(term.right,
                                                    old_var, new_var))
            else:
                return Term('LAM', term.value,
                           right=self.alpha_convert(term.right,
                                                   old_var, new_var))
        elif term.term_type == 'APP':
            return Term('APP',
                        left=self.alpha_convert(term.left, old_var, new_var),
                        right=self.alpha_convert(term.right, old_var, new_var))
        return term

    def substitute(self, term, var, replacement):
        if term is None:
            return None
        if term.term_type == 'VAR':
            return (copy.deepcopy(replacement)
                    if term.value == var else Term('VAR', term.value))
        elif term.term_type == 'LAM':
            if term.value == var:
                return term
            free_in_repl = self.free_vars(replacement)
            if term.value in free_in_repl:
                new_var = self.fresh_var(term.value)
                new_body = self.alpha_convert(term.right,
                                            term.value, new_var)
                new_body = self.substitute(new_body, var, replacement)
                return Term('LAM', new_var, right=new_body)
            else:
                new_body = self.substitute(term.right, var, replacement)
                return Term('LAM', term.value, right=new_body)
        elif term.term_type == 'APP':
            new_left = self.substitute(term.left, var, replacement)
            new_right = self.substitute(term.right, var, replacement)
            return Term('APP', left=new_left, right=new_right)
        return term

    def beta_reduction(self, term):
        self._log(f"Attempt beta reduction: {self.to_latex(term)}")
        if term is None or term.term_type != 'APP':
            self._log("Beta reduction failed: Not APP type or None")
            return None, None
        if term.left and term.left.term_type == 'LAM':
            lambda_term = term.left
            arg = term.right
            reduced_body = self.substitute(lambda_term.right,
                                         lambda_term.value, arg)
            self._log(f"Beta success: {lambda_term.value}->{self.to_latex(arg)}")
            self._log(f"Result: {self.to_latex(reduced_body)}")
            return reduced_body, 'β'
        self._log("Beta failed: Left not LAM")
        return None, None

    def eta_reduction(self, term):
        self._log(f"Attempt eta reduction: {self.to_latex(term)}")
        if term is None or term.term_type != 'LAM':
            self._log("Eta failed: Not LAM type or None")
            return None, None
        var = term.value
        body = term.right
        if (body and body.term_type == 'APP'
            and body.right and body.right.term_type == 'VAR'
            and body.right.value == var
            and var not in self.free_vars(body.left)):
            self._log(f"Eta success: remove redundant λ{var}")
            self._log(f"Result: {self.to_latex(body.left)}")
            return body.left, 'η'
        self._log("Eta reduction failed")
        return None, None

    def reduce_step(self, term):
        self._log(f"reduce_step input: {self.to_latex(term)}")
        if term is None:
            self._log("Null term, return None")
            return None, None

        self.indent_level += 1

        # Prioritize beta reduction
        reduced, rule = self.beta_reduction(term)
        if reduced:
            self.indent_level -= 1
            self._log(f"Beta success, return {self.to_latex(reduced)}")
            return reduced, rule

        # Then eta reduction if enabled
        if self.enable_eta:
            reduced, rule = self.eta_reduction(term)
            if reduced:
                self.indent_level -= 1
                self._log(f"Eta success, return {self.to_latex(reduced)}")
                return reduced, rule

        # Recursively reduce subterms
        if term.term_type == 'LAM':
            reduced_body, rule = self.reduce_step(term.right)
            self.indent_level -= 1
            if reduced_body:
                return (Term('LAM', term.value, right=reduced_body),
                        rule)
            return None, None

        elif term.term_type == 'APP':
            if self.strategy == 'normal':
                reduced_left, rule = self.reduce_step(term.left)
                if reduced_left:
                    self.indent_level -= 1
                    return (Term('APP', left=reduced_left, right=term.right),
                            rule)

                reduced_right, rule = self.reduce_step(term.right)
                self.indent_level -= 1
                if reduced_right:
                    return (Term('APP', left=term.left, right=reduced_right),
                            rule)

            elif self.strategy == 'applicative':
                reduced_right, rule = self.reduce_step(term.right)
                if reduced_right:
                    self.indent_level -= 1
                    return (Term('APP', left=term.left, right=reduced_right),
                            rule)

                reduced_left, rule = self.reduce_step(term.left)
                self.indent_level -= 1
                if reduced_left:
                    return (Term('APP', left=reduced_left, right=term.right),
                            rule)

            self.indent_level -= 1

        else:
            self.indent_level -= 1

        self._log("No reduction")
        return None, None

    def to_latex(self, term: Term) -> str:
        if term.term_type == 'VAR':
            return term.value
        elif term.term_type == 'LAM':
            return f"\\lambda {term.value}. {self.to_latex(term.right)}"
        elif term.term_type == 'APP':
            return f"({self.to_latex(term.left)}~{self.to_latex(term.right)})"

    def latex_history(self, history):
        lines = []
        for i, (_, term) in enumerate(history):
            lines.append(f"\\[{self.to_latex(term)}\\]")
        return "\n".join(lines)

    def evaluate(self, term_or_str, limit=None,
                render_latex=False, latex_image_path="reduction.png"):
        if isinstance(term_or_str, str):
            term = parse_lambda_expr(term_or_str)
        else:
            term = term_or_str

        clock = 0
        current_term = copy.deepcopy(term)
        history = [(clock, copy.deepcopy(current_term))]

        while True:
            if limit and clock >= limit:
                break
            reduced_term, rule = self.reduce_step(current_term)
            if not reduced_term:
                break
            self.event_history.append(
                ReductionEvent(clock, current_term, reduced_term, rule))
            current_term = reduced_term
            clock += 1
            history.append((clock, copy.deepcopy(current_term)))

        if render_latex:
            plt.figure(figsize=(10, 1 + len(history) * 0.6))
            plt.axis('off')
            plt.text(0.05, 1.0, self.latex_history(history),
                    ha='left', va='top', fontsize=12,
                    wrap=True, family='monospace')
            plt.tight_layout()
            plt.savefig(latex_image_path, dpi=300, bbox_inches='tight')
            plt.close()
            self.logger.info(f"LaTeX saved to {latex_image_path}")

        return current_term, history

# Church encodings and combinators
def church_true():
    return Term('LAM', 't',
               right=Term('LAM', 'f', right=Term('VAR', 't')))

def church_false():
    return Term('LAM', 't',
               right=Term('LAM', 'f', right=Term('VAR', 'f')))

def church_zero():
    return Term('LAM', 'f',
               right=Term('LAM', 'x', right=Term('VAR', 'x')))

def church_n(n):
    x = Term('VAR', 'x')
    body = x
    for _ in range(n):
        body = Term('APP', left=Term('VAR', 'f'), right=body)
    return Term('LAM', 'f', right=Term('LAM', 'x', right=body))

def Y_combinator():
    f = Term('VAR', 'f')
    g = Term('VAR', 'g')
    y = Term('VAR', 'y')
    inner_lambda = Term('LAM', 'g',
                       right=Term('APP', left=f,
                                 right=Term('LAM', 'y',
                                           right=Term('APP',
                                                     left=Term('APP',
                                                              left=g, right=g),
                                                     right=y))))
    Y = Term('LAM', 'f',
            right=Term('APP',
                      left=Term('LAM', 'g',
                               right=Term('APP', left=f,
                                         right=Term('APP', left=g, right=g))),
                      right=inner_lambda))
    return Y

# Arithmetic operations
def ISZERO():
    n = Term('VAR', 'n')
    return Term('LAM', 'n',
               right=Term('APP',
                         left=Term('APP', left=n,
                                  right=Term('LAM', '_', right=church_false())),
                         right=church_true()))

def church_and():
    return Term('LAM', 'a', right=Term('LAM', 'b',
              right=Term('APP', left=Term('APP',
                          left=Term('VAR', 'a'),
                          right=Term('VAR', 'b')),
                        right=church_false())))

def church_or():
    return Term('LAM', 'a', right=Term('LAM', 'b',
              right=Term('APP', left=Term('APP',
                          left=Term('VAR', 'a'),
                          right=church_true()),
                        right=Term('VAR', 'b'))))

def church_one():

    return church_n(1)

def PRED():
    return Term('LAM', 'n', right=Term(
        'LAM', 'f', right=Term(
            'LAM', 'x', right=Term(
                'APP',
                left=Term(
                    'APP',
                    left=Term(
                        'APP',
                        left=Term('VAR', 'n'),
                        right=Term(
                            'LAM', 'g', right=Term(
                                'LAM', 'h', right=Term(
                                    'APP',
                                    left=Term('VAR', 'h'),
                                    right=Term(
                                        'APP',
                                        left=Term('VAR', 'g'),
                                        right=Term('VAR', 'f')
                                    )
                                )
                            )
                        )
                    ),
                    right=Term(
                        'LAM', 'u', right=Term('VAR', 'x')
                    )
                ),
                right=Term(
                    'LAM', 'u', right=Term('VAR', 'u')
                )
            )
        )
    ))


def MUL():
    return Term(
        'LAM', 'm',
        right=Term(
            'LAM', 'n',
            right=Term(
                'LAM', 'f',
                right=Term(
                    'APP',
                    left=Term('VAR', 'm'),
                    right=Term(
                        'APP',
                        left=Term('VAR', 'n'),
                        right=Term('VAR', 'f')
                    )
                )
            )
        )
    )



def CONS():
    a = Term('VAR', 'a')
    b = Term('VAR', 'b')
    s = Term('VAR', 's')
    return Term(
        'LAM', 'a',
        right=Term(
            'LAM', 'b',
            right=Term(
                'LAM', 's',
                right=Term(
                    'APP',
                    left=Term(
                        'APP',
                        left=s,
                        right=a
                    ),
                    right=b
                )
            )
        )
    )



def CAR():
    p = Term('VAR', 'p')
    return Term('LAM', 'p',
                right=Term('APP', left=p, right=church_true()))


def CDR():
    p = Term('VAR', 'p')
    return Term('LAM', 'p',
                right=Term('APP', left=p, right=church_false()))


def FACT():
    Y = Y_combinator()
    f = Term('VAR', 'f')
    n = Term('VAR', 'n')

    condition = Term('APP', left=ISZERO(), right=n)
    then_branch = church_one()
    else_branch = Term(
        'APP',
        left=Term(
            'APP',
            left=MUL(),
            right=n
        ),
        right=Term(
            'APP',
            left=f,
            right=Term(
                'APP',
                left=PRED(),
                right=n
            )
        )
    )

    fact_body = Term(
        'LAM', 'f',
        right=Term(
            'LAM', 'n',
            right=Term(
                'APP',
                left=Term(
                    'APP',
                    left=condition,
                    right=then_branch
                ),
                right=else_branch
            )
        )
    )

    return Term('APP', left=Y, right=fact_body)


def church_to_int(term):
    if term.term_type != 'LAM':
        raise ValueError("Not a Church numeral")
    f_var = term.value
    inner = term.right
    if inner.term_type != 'LAM':
        raise ValueError("Not a Church numeral")
    x_var = inner.value
    body = inner.right

    def count_apps(t):
        if t.term_type == 'VAR' and t.value == x_var:
            return 0
        elif (t.term_type == 'APP'
              and t.left.term_type == 'VAR'
              and t.left.value == f_var):
            return 1 + count_apps(t.right)
        else:
            raise ValueError("Malformed Church numeral")

    return count_apps(body)


def reduce_to_church_int(term, interpreter):
    result, _ = interpreter.evaluate(term)
    while result.term_type != 'LAM' or result.right.term_type != 'LAM':
        result, _ = interpreter.evaluate(result)
    return church_to_int(result)


def church_bool_to_int(term):
    if term.term_type != 'LAM':
        raise ValueError("Not a Church boolean")
    inner = term.right
    if inner.term_type != 'LAM':
        raise ValueError("Not a Church boolean")
    return 1 if inner.right.value == term.value else 0
