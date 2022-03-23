
export ROOT_DIR=${PWD}
UNAME := $(shell uname)

# make sure you build parent project first or it won't find the libraries

all: diffmu-wrapper

diffmu-wrapper: wrappermain.cpp
# set linker path on linux
# not sure why I need clang++ or -stdlib=libc++ but it fixes some missing symbol errors
# ifeq ($(UNAME), Linux)
# 	# clang++ -g -Wall wrappermain.cpp -o $@ \
# 	# -I../csrc \
# 	# -stdlib=libc++ \
# 	# -Wl,-rpath='$$ORIGIN' \
# 	# -lwrapper \
# 	# -L./

# 	clang++ -g -Wall wrappermain.cpp -o $@ \
# 	-I../csrc \
# 	-stdlib=libc++ \
# 	-Wl,-rpath='$$ORIGIN' \
# 	-lwrapper \
#   -lstdc++ \
#   -lc++abi \
# 	-L./
# else
	g++ -g -Wall wrappermain.cpp -o diffmu-wrapper \
	-I../csrc \
	-ldiffmu-wrapper \
	-L./
# endif
# set rpath path on mac, see https://medium.com/@donblas/fun-with-rpath-otool-and-install-name-tool-e3e41ae86172
ifeq ($(UNAME), Darwin)
	install_name_tool -add_rpath @executable_path/. wrappermain
endif


run: diffmu-wrapper
	./diffmu-wrapper

clean:
	rm -rf *.o *.a *.dSYM *.dylib wrappermain

.PHONY: clean all run
