
all: acl2s coq dafny racket rosette typed-racket z3

acl2s:
	acl2s < ./acl2s/shared-temperature.lisp

coq:
	coqc -Q ./coq SharedTemperature ./coq/SharedTemperature.v

dafny:
	dafny ./dafny/shared-temperature.dfy

racket:
	racket ./racket/shared-temperature/shared-temperature.rkt

rosette:
	racket ./rosette/rosette-shared-temperature/shared-temperature.rkt

typed-racket:
	racket ./typed-racket/typed-racket-shared-temperature/shared-temperature.rkt

z3:
	z3 -smt2 ./z3/shared-temperature.smt2

.PHONY: all acl2s coq dafny racket rosette typed-racket z3
