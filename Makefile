all:
	${ACL2_SYSTEM_BOOKS}/build/cert.pl proofChallenge.lisp

clean:
	${ACL2_SYSTEM_BOOKS}/build/clean.pl
	$(RM) -rf *.pyc

