import copy
from collections import namedtuple
import matplotlib.pyplot as plt
ReductionEvent = namedtuple("ReductionEvent", "clock term reduced_term rule")

class Term:
    def __init__(self, term_type, value=None, left=None, right=None):
        self.term_type = term_type  # 'VAR', 'LAM', 'APP'
        self.value = value          # 变量名或绑定变量
        self.left = left            # 左子项
        self.right = right          # 右子项

        if self.term_type == 'LAM':
            assert right is not None, f"LAM node with param {value} has no body"
        if self.term_type == 'APP':
            assert left is not None and right is not None, "APP node has None child"

    def __repr__(self):
        if self.term_type == 'VAR':
            return self.value
        elif self.term_type == 'LAM':
            return f"(λ{self.value}.{self.right})"
        elif self.term_type == 'APP':
            return f"({self.left} {self.right})"
        return ""

class LambdaInterpreter:
    def __init__(self, strategy="normal", enable_eta=True):
        self.strategy = strategy
        self.enable_eta = enable_eta  # 控制 η 归约的开关
        self.event_history = []
        self.counter = 0

        import logging
        logging.basicConfig(level=logging.INFO)
        self.logger = logging.getLogger("LambdaInterpreter")

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
                        left=self.alpha_convert(term.left, old_var, new_var),
                        right=self.alpha_convert(term.right, old_var, new_var))
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
        if self.enable_eta:
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
                    # print(f"reduce_step: reduced_left={reduced_left}, term.right={term.right}")
                    return Term('APP', left=reduced_left, right=term.right), rule
                reduced_right, rule = self.reduce_step(term.right)
                if reduced_right is not None:
                    return Term('APP', left=term.left, right=reduced_right), rule
            elif self.strategy == 'applicative':
                reduced_right, rule = self.reduce_step(term.right)
                if reduced_right is not None:
                    return Term('APP', left=term.left, right=reduced_right), rule
                reduced_left, rule = self.reduce_step(term.left)
                if reduced_left is not None:
                    return Term('APP', left=reduced_left, right=term.right), rule

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
            latex = self.to_latex(term)
            lines.append(f"\\[{latex}\\]")
        return "\n".join(lines)

    def evaluate(self, term_or_str, limit=None):
        # 支持字符串输入，简单示例只支持单变量 λx.x
        if isinstance(term_or_str, str):
            # 简单解析例子，复杂请自己扩展
            if term_or_str.strip() == "λx.x":
                term = Term('LAM', 'x', right=Term('VAR', 'x'))
            else:
                raise ValueError("暂不支持复杂字符串解析，请传 Term 对象")
        else:
            term = term_or_str
        clock = 0
        current_term = copy.deepcopy(term)
        history = [(clock, copy.deepcopy(current_term))]
        while True:
            if limit is not None and clock >= limit:
                break
            reduced_term, rule = self.reduce_step(current_term)
            if reduced_term is None:
                break
            self.event_history.append(ReductionEvent(clock, current_term, reduced_term, rule))
            current_term = reduced_term
            clock += 1
            history.append((clock, copy.deepcopy(current_term)))
        return current_term, history


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
    return Term('LAM', 'n',
        right=Term('LAM', 'f',
            right=Term('LAM', 'x',
                right=Term('APP',
                    left=Term('APP',
                        left=Term('APP', left=Term('VAR', 'n'),
                                  right=Term('LAM', 'g',
                                             right=Term('LAM', 'h',
                                                        right=Term('APP',
                                                                   left=Term('VAR', 'h'),
                                                                   right=Term('APP',
                                                                              left=Term('VAR', 'g'),
                                                                              right=Term('VAR', 'f')))))),
                        right=Term('LAM', 'u', right=Term('VAR', 'x'))),
                    right=Term('LAM', 'u', right=Term('VAR', 'u'))))))



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
    Y = Y_combinator()
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

def church_bool_to_int(term):
    # 判断是否是 church_true
    # church_true = λt.λf.t
    # church_false = λt.λf.f
    if term.term_type != 'LAM':
        raise ValueError("Not a Church boolean")
    inner = term.right
    if inner.term_type != 'LAM':
        raise ValueError("Not a Church boolean")
    # 这里检查内层变量是 t 或 f
    body = inner.right
    if body.term_type == 'VAR':
        if body.value == term.value:
            # λt.λf.t  => true
            return 1
        else:
            # λt.λf.f  => false
            return 0
    raise ValueError("Malformed Church boolean")

def church_to_int(term):
    # 逐层剥离 λf.λx.body
    if term.term_type != 'LAM':
        raise ValueError("Not a Church numeral")
    term = term.right
    if term.term_type != 'LAM':
        raise ValueError("Not a Church numeral")
    body = term.right

    # 现在我们遍历 body: f(f(f(...x)))
    count = 0
    while body.term_type == 'APP':
        if body.left.term_type == 'VAR' and body.left.value == 'f':
            count += 1
            body = body.right
        else:
            break

    # 最后一层应该是 VAR 'x'
    if body.term_type == 'VAR' and body.value == 'x':
        return count
    else:
        raise ValueError("Malformed Church numeral")


def term_to_latex(term):
    if term.term_type == 'VAR':
        return term.value
    elif term.term_type == 'LAM':
        return r"\lambda {}.{}".format(term.value, term_to_latex(term.right))
    elif term.term_type == 'APP':
        left = term_to_latex(term.left)
        right = term_to_latex(term.right)
        # 添加括号以避免歧义
        if term.left.term_type in ['LAM', 'APP']:
            left = f"({left})"
        if term.right.term_type in ['LAM', 'APP']:
            right = f"({right})"
        return f"{left} {right}"
    else:
        raise ValueError(f"Unknown term type: {term.term_type}")

def history_to_latex(history):
    lines = []
    for i, term in history:
        latex = term_to_latex(term)
        lines.append(f"{i}:\\quad {latex}")
    return lines

def render_latex_to_image(latex_lines):
    fig, ax = plt.subplots(figsize=(8, len(latex_lines)*0.8))
    ax.axis('off')
    for i, line in enumerate(latex_lines):
        y = 1 - i * 0.15  # 每一行下移一点
        ax.text(0, y, f"${line}$", fontsize=16, ha='left', va='top')
    plt.tight_layout()
    plt.show()

def reduce_to_church_int(term, interpreter):
    result, _ = interpreter.evaluate(term)
    while result.term_type != 'LAM' or result.right.term_type != 'LAM':
        result, _ = interpreter.evaluate(result)
    return church_to_int(result)
#
if __name__ == "__main__":
    two = church_n(2)
    three = church_n(3)
    mul_expr = Term('APP', left=Term('APP', left=MUL(), right=two), right=three)
    interpreter2 = LambdaInterpreter(strategy="normal", enable_eta=False)
    result, _ = interpreter2.evaluate(mul_expr)
    print(church_to_int(result))
#     # print(PRED())
#     # (λx.λy.x y) z
#     term = Term('APP',
#                left=Term('LAM', 'x',
#                         right=Term('LAM', 'y',
#                                   right=Term('APP',
#                                             left=Term('VAR', 'x'),
#                                             right=Term('VAR', 'y')))),
#                right=Term('VAR', 'z'))
#     print("原始项:", term)
#
    interpreter = LambdaInterpreter(strategy="normal", enable_eta=False)
#     final_term, history = interpreter.evaluate(term)
#     #render
#
#
#     print("\n归约历史:")
#     for _, t in history:
#         print(t)
#
#     # 阿尔法转换
#     k = Term('LAM', 'x', right=Term('VAR', 'x'))  # λx.x
#     converted = interpreter.alpha_convert(k, 'x', 'y')
#     print("\n转换前:", k)
#     print("alpha归约转换后:", converted)
#     # 应输出：λy.y
#
#     # eta归约测试
#     eta_term = Term('LAM', 'x',
#                    right=Term('APP',
#                              left=Term('VAR', 'f'),
#                              right=Term('VAR', 'x')))
#     print("\neta可归约项:", eta_term)
#     interpreter2 = LambdaInterpreter(strategy="normal")
#     reduced, _ = interpreter2.eta_reduction(eta_term)
#     print("eta归约结果:", reduced)
#
#     # 输出归约历史
#     print("\n归约历史:")
#     for clock, term in history:
#         print(term)


    fact = FACT()
    input = church_n(4)
    app_term = Term('APP', left=fact, right=input)

    reduced_term, history = interpreter.evaluate(app_term)  # 适当增加归约步数

    print("最终归约结果:", reduced_term)
    print("转换成整数:", church_to_int(reduced_term))

    print("\n阶乘结果:")
    print(reduced_term)
