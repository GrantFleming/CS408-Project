\NeedsTeXFormat{LaTeX2e}

\ProvidesClass{ProgessReport}[2020/09/15 4th Year Report]

\LoadClass[10pt, a4paper]{report}

\RequirePackage[utf8]{inputenc}
\RequirePackage[english]{babel}
\RequirePackage{csquotes}
\RequirePackage[toc, page]{appendix}
\RequirePackage{biblatex}
\RequirePackage{tgpagella}
\RequirePackage[margin=1.2in]{geometry}
\RequirePackage{amssymb}
\RequirePackage{amsmath}
\RequirePackage{ebproof}
\RequirePackage[outputdir=out]{minted}

\newcommand*{\markingscheme}[1]{\gdef\@markingscheme{#1}}
\newcommand*{\regnumber}[1]{\gdef\@regnumber{#1}}
\newcommand*{\supervisor}[1]{\gdef\@supervisor{#1}}

\renewcommand{\familydefault}{\sfdefault}

\setlength{\parskip}{0.5em}

\renewcommand\maketitle{
	\begin{titlepage}%
		\let\footnotesize\small
		\let\footnoterule\relax
		\let \footnote \thanks
		\null\vfil
		\vskip 60\p@
		\begin{center}%
                  {\LARGE Progress Report \par}
                  \vskip 5em
                  \begin{tabular}{@{}p{11em}p{15em}@{}}
                    {\large Project Title:} & {\large \@title} \\[1em]
                    {\large Marking Scheme:} & {\large \@markingscheme} \\[1em]
                    {\large Student Name:} & {\large \@author} \\[1em]
                    {\large Registration Number:} & {\large\@regnumber} \\[1em]
                    {\large Supervised By:} & {\large \@supervisor} \\[1em]
                  \end{tabular}
	          \vskip 5em
		  {\large Submitted for the Degree of B.Sc. in Computer Science \@date \par}
		  \vskip 1.5em
		  {\emph{Except where explicitly stated all work in
                      this report, including appendices, is my own and
                      was carried out during my final year. It has not
                      been submitted for assessment in any other context.} \par}
		  \vskip 8em
                  \begin{tabular}{@{}p{15em}p{18em}@{}}
		     Signed:        & \hrulefill \\[1em]
		     & \@author \\[1em]
                     Date: & 23/11/2020 \\[1em]
		  \end{tabular}
		\end{center}\par
		\vfill
		\noindent
		I agree to this material being made available in whole or in part to benefit the education of future students.
		\vfil\null
	\end{titlepage}%
	\setcounter{footnote}{0}%
	\global\let\thanks\relax
	\global\let\maketitle\relax
	\global\let\@thanks\@empty
	\global\let\@author\@empty
	\global\let\@regnumber\@empty
	\global\let\@date\@empty
	\global\let\@title\@empty
        \global\let\@supervisor\@empty
	\global\let\title\relax
	\global\let\author\relax
	\global\let\regnumber\relax
	\global\let\date\relax
	\global\let\and\relax
        \global\let\supervisor\relax
}
