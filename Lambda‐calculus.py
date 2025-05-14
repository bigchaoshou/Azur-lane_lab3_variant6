import copy
from collections import namedtuple

ReductionEvent = namedtuple("ReductionEvent", "clock term reduced_term rule")

class Term:
    def __init__(self, term_type, value=None, left=None, right=None):
        self.term_type = term_type  # 'VAR', 'LAM', 'APP'
        self.value = value          # 变量名或绑定变量
        self.left = left            # 左子项
        self.right = right          # 右子项

    def __repr__(self):
        if self.term_type == 'VAR':
            return self.value
        elif self.term_type == 'LAM':
            return f"(λ{self.value}.{self.right})"
        elif self.term_type == 'APP':
            return f"({self.left} {self.right})"
        return ""

class LambdaInterpreter:
    def __init__(self, strategy="normal"):
        self.strategy = strategy
        self.event_history = []
        self.counter = 0

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
            return self.free_vars(term.left) | self.free_vars(term.right)
        return set()

    def alpha_convert(self, term, old_var, new_var):
        if term is None:
            return None
        if term.term_type == 'VAR':
            return Term('VAR', new_var) if term.value == old_var else term
        elif term.term_type == 'LAM':
            if term.value == old_var:
                return Term('LAM', new_var, right=self.alpha_convert(term.right, old_var, new_var))
            else:
                return Term('LAM', term.value, right=self.alpha_convert(term.right, old_var, new_var))
        elif term.term_type == 'APP':
            return Term('APP',
                        self.alpha_convert(term.left, old_var, new_var),
                        self.alpha_convert(term.right, old_var, new_var))
        return term

    def substitute(self, term, var, replacement):
        if term is None:
            return None
        if term.term_type == 'VAR':
            return copy.deepcopy(replacement) if term.value == var else Term('VAR', term.value)
        elif term.term_type == 'LAM':
            if term.value == var:
                return term
            free_in_repl = self.free_vars(replacement)
            if term.value in free_in_repl:
                new_var = self.fresh_var(term.value)
                new_body = self.alpha_convert(term.right, term.value, new_var)
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
        if term is None or term.term_type != 'APP':
            return None, None
        if term.left is not None and term.left.term_type == 'LAM':
            lambda_term = term.left
            arg = term.right
            reduced_body = self.substitute(lambda_term.right, lambda_term.value, arg)
            return reduced_body, 'β'
        return None, None

    def eta_reduction(self, term):
        if term is None or term.term_type != 'LAM':
            return None, None
        var = term.value
        body = term.right
        if body is not None and body.term_type == 'APP':
            if body.right is not None and body.right.term_type == 'VAR' and body.right.value == var:
                if var not in self.free_vars(body.left):
                    return body.left, 'η'
        return None, None

    def reduce_step(self, term):
        if term is None:
            return None, None

        # 优先尝试β归约
        reduced, rule = self.beta_reduction(term)
        if reduced is not None:
            return reduced, rule

        # 其次尝试η归约
        reduced, rule = self.eta_reduction(term)
        if reduced is not None:
            return reduced, rule

        # 递归处理子项
        if term.term_type == 'LAM':
            reduced_body, rule = self.reduce_step(term.right)
            if reduced_body is not None:
                return Term('LAM', term.value, right=reduced_body), rule

        elif term.term_type == 'APP':
            if self.strategy == 'normal':
                reduced_left, rule = self.reduce_step(term.left)
                if reduced_left is not None:
                    return Term('APP', reduced_left, term.right), rule
                reduced_right, rule = self.reduce_step(term.right)
                if reduced_right is not None:
                    return Term('APP', term.left, reduced_right), rule
            elif self.strategy == 'applicative':
                reduced_right, rule = self.reduce_step(term.right)
                if reduced_right is not None:
                    return Term('APP', term.left, reduced_right), rule
                reduced_left, rule = self.reduce_step(term.left)
                if reduced_left is not None:
                    return Term('APP', reduced_left, term.right), rule

        return None, None

    def evaluate(self, term, limit=100):
        clock = 0
        current_term = copy.deepcopy(term)
        history = [(clock, copy.deepcopy(current_term))]
        while clock < limit:
            reduced_term, rule = self.reduce_step(current_term)
            if reduced_term is None:
                break
            self.event_history.append(ReductionEvent(clock, current_term, reduced_term, rule))
            current_term = reduced_term
            clock += 1
            history.append((clock, copy.deepcopy(current_term)))
        return current_term, history

    def visualize(self, history):
        res = ["digraph G {", " rankdir=LR;"]
        for i, (clock, term) in enumerate(history):
            res.append(f' node_{i} [label="{term}"];')
            if i > 0:
                res.append(f' node_{i-1} -> node_{i} [label="Step {clock}"];')
        res.append("}")
        return "\n".join(res)

# Church 布尔值定义
# 基础定义
def church_true():
    return Term('LAM', 't', right=Term('LAM', 'f', right=Term('VAR', 't')))


def church_false():
    return Term('LAM', 't', right=Term('LAM', 'f', right=Term('VAR', 'f')))


def church_zero():
    return Term('LAM', 'f', right=Term('LAM', 'x', right=Term('VAR', 'x')))


def church_one():
    return church_n(1)

def Y_combinator():
    # 内部变量定义
    f = Term('VAR', 'f')
    g = Term('VAR', 'g')
    y = Term('VAR', 'y')

    # 构造右侧的 (λg.f (λy.g g y))
    inner_lambda = Term('LAM', 'g',
                        right=Term('APP',
                                   left=f,
                                   right=Term('LAM', 'y',
                                              right=Term('APP',
                                                         left=Term('APP', left=g, right=g),
                                                         right=y))))

    # 构造整体结构
    Y = Term('LAM', 'f',
             right=Term('APP',
                        left=Term('LAM', 'g',
                                  right=Term('APP',
                                             left=f,
                                             right=Term('APP', left=g, right=g))),
                        right=inner_lambda))

    return Y

# 列表操作
def CONS():
    a = Term('VAR', 'a')
    b = Term('VAR', 'b')
    s = Term('VAR', 's')
    return Term('LAM', 'a',
                right=Term('LAM', 'b',
                           right=Term('LAM', 's',
                                      right=Term('APP',
                                                 left=Term('APP', left=s, right=a),
                                                 right=b))))


def CAR():
    p = Term('VAR', 'p')
    return Term('LAM', 'p',
                right=Term('APP', left=p, right=church_true()))


def CDR():
    p = Term('VAR', 'p')
    return Term('LAM', 'p',
                right=Term('APP', left=p, right=church_false()))


# 算术操作
def PRED():
    n = Term('VAR', 'n')
    t = Term('VAR', 'T')  # 假设T已定义为CONS生成器
    return Term('LAM', 'n',
                right=Term('APP',
                           left=CDR(),
                           right=Term('APP',
                                      left=Term('APP', left=n, right=t),
                                      right=Term('APP',
                                                 left=Term('APP', left=CONS(), right=church_zero()),
                                                 right=church_zero()))))


def ISZERO():
    n = Term('VAR', 'n')
    return Term('LAM', 'n',
                right=Term('APP',
                           left=Term('APP', left=n, right=Term('LAM', '_', right=church_false())),
                           right=church_true()))

def church_n(n):
    x = Term('VAR', 'x')
    body = x
    for _ in range(n):
        body = Term('APP', left=Term('VAR', 'f'), right=body)
    return Term('LAM', 'f', right=Term('LAM', 'x', right=body))


def MUL():
    return Term('LAM', 'm',
                right=Term('LAM', 'n',
                           right=Term('LAM', 'f',
                                      right=Term('APP',
                                                 left=Term('VAR', 'm'),
                                                 right=Term('APP',
                                                            left=Term('VAR', 'n'),
                                                            right=Term('VAR', 'f'))))))

# 最终阶乘函数
def FACT():
    Y = Y_combinator()  # 使用之前定义的Y组合子
    f = Term('VAR', 'f')
    n = Term('VAR', 'n')

    condition = Term('APP', left=ISZERO(), right=n)
    then_branch = church_one()
    else_branch = Term('APP',
                       left=Term('APP', left=MUL(), right=n),
                       right=Term('APP',
                                  left=f,
                                  right=Term('APP', left=PRED(), right=n)))

    fact_body = Term('LAM', 'f',
                     right=Term('LAM', 'n',
                                right=Term('APP',
                                           left=Term('APP', left=condition, right=then_branch),
                                           right=else_branch)))

    return Term('APP', left=Y, right=fact_body)

if __name__ == "__main__":
    # (λx.λy.x y) z
    term = Term('APP',
               left=Term('LAM', 'x',
                        right=Term('LAM', 'y',
                                  right=Term('APP',
                                            left=Term('VAR', 'x'),
                                            right=Term('VAR', 'y')))),
               right=Term('VAR', 'z'))
    print("原始项:", term)

    interpreter = LambdaInterpreter(strategy="normal")
    final_term, history = interpreter.evaluate(term)
    print("\n归约历史:")
    for _, t in history:
        print(t)
    # 阿尔法转换
    k = Term('LAM', 'x', right=Term('VAR', 'x'))  # λx.x
    converted = interpreter.alpha_convert(k, 'x', 'y')
    print("转换前:", k)
    print("转换后:", converted)
    # 应输出：λy.y

    # η归约测试
    eta_term = Term('LAM', 'x',
                   right=Term('APP',
                             left=Term('VAR', 'f'),
                             right=Term('VAR', 'x')))
    print("\nη可归约项:", eta_term)
    reduced, _ = interpreter.eta_reduction(eta_term)
    print("η归约结果:", reduced)

    # 输出归约历史
    print("\n归约历史:")
    for clock, term in history:
        print(term)

    # Church 数字3
    three = church_n(3)
    print("Church数字3:", three)

    interpreter = LambdaInterpreter(strategy="normal")
    fact = FACT()
    input3 = church_n(3)
    app_term = Term('APP', left=fact, right=input3)
    # mul=mult()
    # print(mul)
    print(fact)
    # print(church_false)
    final_term, history = interpreter.evaluate(app_term)
    # print(history)
    print("\n阶乘结果:")
    print(final_term)
