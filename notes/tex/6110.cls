\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{6110}

\DeclareOption{hw}{\hwtrue}
\DeclareOption{handout}{\handouttrue}
\DeclareOption{all}{\alltrue}
\DeclareOption{exam}{\examtrue}
\DeclareOption{solution}{\solutiontrue}
\DeclareOption{instructions}{\instructionstrue}

% Package options:
%
% default is single lecture
% hw: homework
% handout: handout
% all: lectures + hw
% exam: exam
% solution: exam solution
% instructions: exam instructions
%
\newif\ifhw\hwfalse
\newif\ifhandout\handoutfalse
\newif\ifall\allfalse
\newif\ifexam\examfalse
\newif\ifsolution\solutionfalse
\newif\ifinstructions\instructionsfalse
\ProcessOptions

\ifall\LoadClass{book}\else\LoadClass{article}\fi

\RequirePackage{amsmath,amssymb,amsthm,amsfonts,latexsym,graphicx,alltt,url,stmaryrd}
\RequirePackage{bbm,wasysym,wrapfig,bussproofs}
\RequirePackage[svgnames]{xcolor}
\RequirePackage[small,bf]{caption}
\RequirePackage{tikz}
\RequirePackage{mathpartir}
\usetikzlibrary{automata,backgrounds,shapes,arrows,positioning,calc,fit}
\usetikzlibrary{decorations,decorations.pathreplacing,decorations.pathmorphing}
\usepackage{proof,code}
\usepackage[sfcode]{ttquot}
%\usepackage{angle}

\newcommand{\coursenumber}{CS 6110}
\newcommand{\coursename}{Advanced Programming Languages}
\newcommand{\semester}{Spring 2017}
\newcommand{\abbrsem}{S17}

\RequirePackage{6110}
\RequirePackage{exam}

\newcounter{lecture}
\ifall
\renewcommand\thesection{\thelecture.\arabic{section}}
\renewcommand\theequation{\thelecture.\arabic{equation}}
\setcounter{tocdepth}{1}
\fi

\newcommand\lecture[1]{\clearpage\ifall\relax\else\setcounter{page}1\fi\def\@lecture{Lecture #1}\setcounter{lecture}{#1}\setcounter{section}{0}}
\newcommand\lectures[2]{\clearpage\ifall\relax\else\setcounter{page}1\fi\def\@lecture{Lectures #1--#2}\setcounter{lecture}{#1}\setcounter{section}{0}}
\newcommand\handout[1]{\clearpage\ifall\relax\else\setcounter{page}1\fi\def\@lecture{Handout #1}\setcounter{section}{0}}
\newcommand\assignment[2][release]{\clearpage\ifall\relax\else\setcounter{page}1\fi\def\@homework{#2}}
\newcommand\duedate[1]{\def\@duedate{#1}}

\def\@lecture{\ClassError{6110}{No \noexpand\lecture or \noexpand\handout given}{You must specify a lecture or handout number}}
\def\@date{\ClassError{6110}{No \noexpand\date given}{You must specify a date}}
\def\@duedate{\ClassError{6110}{No \noexpand\duedate given}{You must specify a due date}}
\def\@homework{\ClassError{6110}{No \noexpand\assignment given}{You must specify an assignment number}}
\def\@title{\ClassError{6110}{No \noexpand\title given}{You must specify a title}}

\renewcommand\maketitle{
\clearpage
\begin{flushleft}
{\large\textsf{\coursenumber~\abbrsem~\@lecture \hfill \@title \hfill}}\\
\hrulefill
\end{flushleft}
\ifall
\addcontentsline{toc}{chapter}{\@lecture: \@title}%
\thispagestyle{plain}%
\pagestyle{myheadings}%
\markboth{\@lecture: \@title}{\@lecture: \@title}%
\fi
}

\ifhandout
\renewcommand{\rmdefault}{ptm}
\renewcommand\maketitle{
\begin{flushleft}
{\large
\textsf{\coursenumber~\abbrsem~Handout \@handout \hfill \@title \hfill \@date}}\\
\hrulefill
\end{flushleft}}
\fi

\def\@hwheader{
\large\sf
\coursenumber~\semester\hfill Assignment \@homework\ifsolution~Solutions\fi\\[3pt]
\coursename\ifsolution\else\hfill Due: \@duedate\fi
}

\newcommand\homeworktitles{
\renewcommand\maketitle{
\clearpage
%\pagestyle{plain}
%\leftmargini=14pt
\parindent=0pt
{
\@hwheader

\hrulefill
}}
}

\ifhw
\homeworktitles
\fi

\ifsolution
\usepackage{xspace}
\newenvironment{solution}{\par\noindent{\bf Solution}:\xspace}{}
\else
\usepackage{comment}
\excludecomment{solution}
\fi

\ifsolution
\newcommand\solutiontext{{\hfil\LARGE\bf Solutions\hfil}}
\else
\newcommand\solutiontext{}
\fi

\newcommand\examtitles{
\renewcommand\maketitle{
%\clearpage
%\pagestyle{plain}
%\leftmargini=14pt
%\parindent=0pt
\begin{center}
{\large
\textsf{\coursenumber~\semester\hfill \@title \hfill \@date}}\\
\hrulefill
\end{center}
%\ifsolution{\hfil\LARGE\bf Solutions\hfil}\fi
\solutiontext
\instructiontext
}
}

\ifexam
\examtitles
\fi

\AtBeginDocument{
\ifall
\pagenumbering{roman}
\pagestyle{myheadings}
\markboth{Contents}{Contents}
\tableofcontents
\clearpage
\pagenumbering{arabic}
\fi
}

\parindent=0pt
\parskip=1em

\AtEndDocument{\label{LastPage}}
