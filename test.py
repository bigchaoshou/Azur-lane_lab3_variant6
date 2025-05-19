import pytest
from lambda_calcu import (
    Term, LambdaInterpreter,
    church_true, church_false, church_zero, church_one, church_n,
    ISZERO, PRED, MUL, church_to_int, church_bool_to_int,
    CONS, CAR, CDR,
    Y_combinator, FACT, reduce_to_church_int
)

@pytest.fixture
def interpreter():
    return LambdaInterpreter(strategy='normal', enable_eta=True)

@pytest.fixture
def interpreter2():
    return LambdaInterpreter(strategy='applicative', enable_eta=True)

@pytest.fixture
def interpreter3():
    return LambdaInterpreter(strategy='normal', enable_eta=False)

@pytest.fixture
def interpreter4():
    return LambdaInterpreter(strategy='applicative', enable_eta=False)

def test_church_boolean(interpreter):
    assert church_bool_to_int(church_true()) == 1
    assert church_bool_to_int(church_false()) == 0

def test_church_zero_one(interpreter):
    assert church_to_int(church_zero()) == 0
    assert church_to_int(church_one()) == 1

def test_iszero(interpreter):
    term1 = Term('APP', left=ISZERO(), right=church_zero())
    term2 = Term('APP', left=ISZERO(), right=church_one())
    result1, _ = interpreter.evaluate(term1)
    result2, _ = interpreter.evaluate(term2)
    assert church_bool_to_int(result1) == 1
    assert church_bool_to_int(result2) == 0

def test_pred(interpreter3):
    two = church_n(2)
    pred_two = Term('APP', left=PRED(), right=two)
    result, _ = interpreter3.evaluate(pred_two)
    print(result)
    assert church_to_int(result) == 1


    zero = church_zero()
    pred_zero = Term('APP', left=PRED(), right=zero)
    result, _ = interpreter3.evaluate(pred_zero)
    assert church_to_int(result) == 0

def test_mul():
    interpreter = LambdaInterpreter(strategy="normal", enable_eta=False)
    two = church_n(2)
    three = church_n(3)
    mul_expr = Term('APP', left=Term('APP', left=MUL(), right=two), right=three)
    result, _ = interpreter.evaluate(mul_expr)
    assert church_to_int(result) == 6

def test_cons_car_cdr(interpreter3):
    one = church_one()
    two = church_n(2)
    cons_expr = Term('APP', left=Term('APP', left=CONS(), right=one), right=two)
    car_expr = Term('APP', left=CAR(), right=cons_expr)
    cdr_expr = Term('APP', left=CDR(), right=cons_expr)
    result_car, _ = interpreter3.evaluate(car_expr)
    result_cdr, _ = interpreter3.evaluate(cdr_expr)
    print(result_car)
    print(result_cdr)
    assert church_to_int(result_car) == 1
    assert church_to_int(result_cdr) == 2

def test_y_combinator_fact(interpreter3):
    fact = FACT()
    input = church_n(4)
    app_term = Term('APP', left=fact, right=input)
    reduced_term, history = interpreter3.evaluate(app_term)
    assert church_to_int(reduced_term) == 24
