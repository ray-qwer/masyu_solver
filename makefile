masyu: clean File.o Proof.o Solver.o masyu.o
	g++ -o $@ -std=c++11 -g File.o Proof.o Solver.o masyu.o

File.o: File.cpp
	g++ -c -std=c++11 -g File.cpp

Proof.o: Proof.cpp
	g++ -c -std=c++11 -g Proof.cpp

Solve.o: Solver.cpp
	g++ -c -std=c++11 -g Solver.cpp

masyu.o: masyu.cpp
	g++ -c -std=c++11 -g masyu.cpp

clean:
	rm -f *.o masyu tags
