\NeedsTeXFormat{LaTeX2e}

\ProvidesClass{FinalYearReport}[2020/09/15 4th Year Report]

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

\renewcommand{\familydefault}{\sfdefault}

\setlength{\parskip}{0.5em}

% 								Custom title page
%								---------------------------

\renewcommand\maketitle{
	\begin{titlepage}%
		\let\footnotesize\small
		\let\footnoterule\relax
		\let \footnote \thanks
		\null\vfil
		\vskip 60\p@
		\begin{center}%
			{\LARGE \@title \par}%
			\vskip 3em%
			{\large
				\lineskip .75em%
				\begin{tabular}[t]{c}%
					\@markingscheme
				\end{tabular}\par}%
			\vskip 1.5em%
						{\large
				\lineskip .75em%
				\begin{tabular}[t]{c}%
					\@regnumber
				\end{tabular}\par}%
			\vskip 1.5em%
						{\large
				\lineskip .75em%
				\begin{tabular}[t]{c}%
					\@author
				\end{tabular}\par}%
			\vskip 1.5em%
			{\large Submitted for the Degree of B.Sc. in Computer Science \@date \par}%       % Set date in \large size.
			\vskip 1.5em%
			{\emph{Except where explicitly stated all work in this report, including appendices, is my own and was carried out during my final year. It has not been submitted for assessment in any other context.} \par}
			\vskip 3em%
			{ \begin{tabular}{@{}p{3.1em}p{18em}@{}}
					Signed: & \hrulefill \\[1em]
					& \centering{\@author} \\
				\end{tabular} \par}
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
	\global\let\title\relax
	\global\let\author\relax
	\global\let\regnumber\relax
	\global\let\date\relax
	\global\let\and\relax
}
