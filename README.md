# define vs define-syntax vs define-for-syntax

| form                      | bind-phase | value-phase | use at phase 0                                   | use at phase 1                                |
|---------------------------|------------|-------------|--------------------------------------------------|-----------------------------------------------|
| `(define x e)`            | 0          | 0           | `x` gets value of `e`                            | N/A                                           |
| `(define-syntax x e)`     | 0          | 1           |  `(x ....)` macro call; `e` transformer function |  `(syntax-local-value #'x)` gets value of `e` |
| `(define-for-syntax x e)` | 1          | 1           | N/A                                              | `x` gets value of `e`                         |
