BOOKS = smallest-coefficient-step.lisp maxmin.lisp minimal-fractions.lisp \
        pigeon.lisp min.lisp

all:
	${ACL2_SYSTEM_BOOKS}/build/cert.pl ${JOBS} ${BOOKS}

clean:
	${ACL2_SYSTEM_BOOKS}/build/clean.pl
	$(RM) -rf *.pyc
