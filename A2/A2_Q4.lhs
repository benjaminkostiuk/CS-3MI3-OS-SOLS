\documentclass[12pt, fleqn]{article}
%include polycode.fmt

\usepackage[utf8]{inputenc}
\usepackage{graphicx}
\usepackage{paralist}
\usepackage{booktabs}
\usepackage{hyperref}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{color}
\usepackage[nounderscore]{syntax}
\usepackage{mdwtab}

\begin{document}

\renewcommand{\texttt}[1]{\OldTexttt{\color{teal}{#1}}}
\newcommand{\pnote}[1]{{\langle \text{#1} \rangle}}
\newcommand{\mname}[1]{\mbox{\sf #1}}


% \setlength{\parindent}{0pt}
\setlength {\topmargin} {-.15in}
\oddsidemargin 0mm
\evensidemargin 0mm
\textwidth 160mm
\textheight 200mm

\pagestyle {plain}
\pagenumbering{arabic}

\newcounter{stepnum}

\title{3MI3 Assignment 2 Solution}
\author{x}
\date{\today}

\begin{center}
    {\large \textbf{COMPSCI 3MI3}}\\[8mm]
    {\huge \textbf{Assignment 2}}\\[6mm]
\end{center}

\medskip

\section{Solution Set}

\subsection{Q4}

\begin{enumerate}

\item[(a)]
We define the syntax for Untyped Arithemtic Expressions in Haskell as follows:
\begin{code}
module A2 where

data UAETerm = 
      T     -- True
    | F     -- False
    | Zero
    | IfThenElse UAETerm UAETerm UAETerm
    | Succ UAETerm
    | Pred UAETerm
    | IsZero UAETerm
    deriving (Eq, Show)
\end{code}

\item[(b)]
We define the following unary Haskell functions to encode the given arithmetic expressions.

\begin{code}
-- (1)
exp1 :: UAETerm
exp1 = Succ $ Succ $ Succ Zero

-- (2)
exp2 :: UAETerm
exp2 = Succ $ Pred $ IsZero $ Succ T

-- (3)
exp3 :: UAETerm
exp3 = IfThenElse x y z
    where
        x = IsZero $ Succ $ Pred Zero
        y = Pred Zero
        z = Succ $ Succ $ Succ Zero
\end{code}

\end{enumerate}

\section{Instructions}

Load this file into ghci with \verb|ghci A2_Q4.lhs|.

\end{document}