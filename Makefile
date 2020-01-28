all:
	${ACL2_SYSTEM_BOOKS}/build/cert.pl smallest-coefficient-step.lisp maxmin.lisp minimal-fractions.lisp

clean:
	${ACL2_SYSTEM_BOOKS}/build/clean.pl
	$(RM) -rf *.pyc

