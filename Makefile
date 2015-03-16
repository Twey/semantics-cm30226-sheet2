all: latex/answers.pdf

latex/Defs.tex: Defs.lagda
	agda -i /home/twey/.nix-profile/share/agda -i . --latex Defs.lagda

latex/Problem1.tex: Problem1.lagda
	agda -i /home/twey/.nix-profile/share/agda -i . --latex Problem1.lagda

latex/answers.pdf: latex/Defs.tex latex/Problem1.tex latex/answers.tex
	cd latex; pdflatex answers.tex
