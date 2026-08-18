`define M(A, B=x) A+B
`M(a, b)
`M(a)
`M(a, )
`define N(A=1, B=2, C=3) A-B-C
`N()
`N(9)
`N(9, 8)
`N(9, 8, 7)
`define P(A, B={1,2}) A-B
`P(p)
`P(p, {3,4})
