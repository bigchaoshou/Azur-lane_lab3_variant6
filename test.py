import matplotlib.pyplot as plt

def render_latex_to_image(latex_expr):
    fig, ax = plt.subplots()
    ax.axis('off')
    ax.text(0.5, 0.5, f"${latex_expr}$", fontsize=20, ha='center', va='center')
    plt.show()

render_latex_to_image(r"\lambda x.((\lambda y.y)\ x)")
