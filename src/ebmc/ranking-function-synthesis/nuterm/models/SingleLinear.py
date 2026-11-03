import torch.nn as nn
import sympy as sp


class SingleLinear(nn.Module):

    def __init__(self, input_dim, input_vars=None):
        super(SingleLinear, self).__init__()

        if input_vars is not None:
            self.input_vars = input_vars

        self.fc1 = nn.Linear(input_dim, 1, bias=False)

    def forward(self, state):
        state = self.fc1(state)
        return state

    def get_weights(self):
        return self.fc1.weight.data.numpy()

    def sympy_expr(self):
        expr = sp.Matrix(sp.symbols(self.input_vars, real=True))  # Careful this changed
        return self.get_weights() * expr

    def sympy_rounded_expr(self):
        expr = sp.Matrix(sp.symbols(self.input_vars, real=True))  # Careful this changed
        return self.get_weights().round() * expr

    def print_sympy(self):
        expr1 = self.sympy_expr()

        for e in expr1:
            print(e)
        print("After rounding:")

        expr = self.sympy_rounded_expr()
        for e in expr:
            print(e)