\NeedsTeXFormat{LaTeX2e}

\ProvidesClass{FinalYearReport}[2020/09/15 4th Year Report]

\LoadClass[11pt, a4paper]{report}

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
\newcommand*{\secondmarker}[1]{\gdef\@secondmarker{#1}}

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
                  {\LARGE Project Report \par}
                  \vskip 4em
                  \begin{tabular}{@{}p{11em}p{15em}@{}}
                    {\large Project Title:} & {\large \@title} \\[1em]
                    {\large Marking Scheme:} & {\large \@markingscheme} \\[1em]
                    {\large Student Name:} & {\large \@author} \\[1em]
                    {\large Registration Number:} & {\large\@regnumber} \\[1em]
                    {\large Supervised By:} & {\large \@supervisor} \\[1em]
                    {\large Second Marker:} & {\large \@secondmarker} \\[1em]
                  \end{tabular}
	          \vskip 3em
		  {\large Submitted for the Degree of B.Sc. in Computer Science \@date \par}
		  \vskip 1.5em
		  {\emph{Except where explicitly stated all work in
                      this report, including appendices, is my own and
                      was carried out during my final year. It has not
                      been submitted for assessment in any other context.} \par}
		  \vskip 3em
                  \begin{tabular}{@{}p{15em}p{18em}@{}}
		     Signed:        & \hrulefill \\[1em]
		     & \@author \\[1em]
                     Date: & 29/03/2021 \\[1em]
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

%timeline stuff
\usepackage{charter}
\usepackage{environ}
\usepackage{tikz}
\usetikzlibrary{calc,matrix}

% code by Andrew:
% http://tex.stackexchange.com/a/28452/13304
\makeatletter
\let\matamp=&
\catcode`\&=13
\makeatletter
\def&{\iftikz@is@matrix
  \pgfmatrixnextcell
  \else
  \matamp
  \fi}
\makeatother

\newcounter{lines}
\def\endlr{\stepcounter{lines}\\}

\newcounter{vtml}
\setcounter{vtml}{0}

\newif\ifvtimelinetitle
\newif\ifvtimebottomline
\tikzset{description/.style={
  column 2/.append style={#1}
 },
 timeline color/.store in=\vtmlcolor,
 timeline color=red!80!black,
 timeline color st/.style={fill=\vtmlcolor,draw=\vtmlcolor},
 use timeline header/.is if=vtimelinetitle,
 use timeline header=false,
 add bottom line/.is if=vtimebottomline,
 add bottom line=false,
 timeline title/.store in=\vtimelinetitle,
 timeline title={},
 line offset/.store in=\lineoffset,
 line offset=4pt,
}

\NewEnviron{vtimeline}[1][]{%
\setcounter{lines}{1}%
\stepcounter{vtml}%
\begin{tikzpicture}[column 1/.style={anchor=east},
 column 2/.style={anchor=west},
 text depth=0pt,text height=1ex,
 row sep=1ex,
 column sep=1em,
 #1
]
\matrix(vtimeline\thevtml)[matrix of nodes]{\BODY};
\pgfmathtruncatemacro\endmtx{\thelines-1}
\path[timeline color st] 
($(vtimeline\thevtml-1-1.north east)!0.5!(vtimeline\thevtml-1-2.north west)$)--
($(vtimeline\thevtml-\endmtx-1.south east)!0.5!(vtimeline\thevtml-\endmtx-2.south west)$);
\foreach \x in {1,...,\endmtx}{
 \node[circle,timeline color st, inner sep=0.15pt, draw=white, thick] 
 (vtimeline\thevtml-c-\x) at 
 ($(vtimeline\thevtml-\x-1.east)!0.5!(vtimeline\thevtml-\x-2.west)$){};
 \draw[timeline color st](vtimeline\thevtml-c-\x.west)--++(-3pt,0);
 }
 \ifvtimelinetitle%
  \draw[timeline color st]([yshift=\lineoffset]vtimeline\thevtml.north west)--
  ([yshift=\lineoffset]vtimeline\thevtml.north east);
  \node[anchor=west,yshift=16pt,font=\large]
   at (vtimeline\thevtml-1-1.north west) 
   {\textsc{Timeline \thevtml}: \textit{\vtimelinetitle}};
 \else%
  \relax%
 \fi%
 \ifvtimebottomline%
   \draw[timeline color st]([yshift=-\lineoffset]vtimeline\thevtml.south west)--
  ([yshift=-\lineoffset]vtimeline\thevtml.south east);
 \else%
   \relax%
 \fi%
\end{tikzpicture}
}
% end timeline stuff

