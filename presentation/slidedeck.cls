%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Copyright 2015 - Jan de Muijnck-Hughes
%%
%% This work may be distributed and/or modified under the  conditions
%% of the LaTeX Project Public License, either version 1.3c of this
%% license or (at your option) any later version.
%%
%% The latest version of this license can be found at:
%%    http://www.latex-project.org/lppl.txt
%% and version 1.3 or later is part of all distributions of LaTeX
%% version 2005/12/01 or later.
%%
%% This work has the LPPL maintenance status `maintained'.
%%
%% The Current Maintainer of this work is Jan de Muijnck-Hughes
%%
%% This work consists of the file: slidedeck.cls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{slidedeck}[2018/01/22 v2018.01.22 slidedeck]

\RequirePackage{ifthen}
\RequirePackage{etoolbox}

%% ----------------------------------------------------------------- [ Options ]
%% Booleans
\newboolean{sectionpages}
\setboolean{sectionpages}{false}

\newboolean{navigation}
\setboolean{navigation}{true}

\newboolean{infofoot}
\setboolean{infofoot}{false}

\newboolean{speakernotes}
\setboolean{speakernotes}{false}

\newboolean{gloss}
\setboolean{gloss}{false}

\newboolean{biblio}
\setboolean{biblio}{false}

\newboolean{talkinghead}
\setboolean{talkinghead}{false}

\newboolean{stripfonts}
\setboolean{stripfonts}{false}

%% Options

\DeclareOption{stripfonts}
{%
  \setboolean{stripfonts}{true}
}

\DeclareOption{sectionpages}
{%
  \setboolean{sectionpages}{true}
}

\DeclareOption{navigationOff}
{%
  \setboolean{navigation}{false}
}

\DeclareOption{speakernotes}
{%
  \setboolean{speakernotes}{true}
}

\DeclareOption{gloss}
{
  \setboolean{gloss}{true}
}

\DeclareOption{biblio}
{
  \setboolean{biblio}{true}
}

\DeclareOption{infofoot}
{%
  \setboolean{infofoot}{true}
}

\DeclareOption{talkinghead}
{%
   \setboolean{talkinghead}{true}
}

\DeclareOption*{
  \PassOptionsToClass{\CurrentOption}{beamer}
}

\ProcessOptions\relax%

\LoadClass{beamer}

% ------------------------------------ [ Fix LaTex Packages ]

\RequirePackage[l2tabu,orthodox]{nag}
\RequirePackage[utf8]{inputenc}
\RequirePackage[T1]{fontenc}
\RequirePackage[strict=true]{csquotes}
\RequirePackage{babel}

\RequirePackage[protrusion=true, expansion=true]{microtype}
\RequirePackage[iso,
                cleanlook]{isodate}
\RequirePackage{relsize}
\RequirePackage{adjustbox}

\RequirePackage{xspace}
\RequirePackage{xcolor}
\RequirePackage{pgffor}
\RequirePackage{pgfpages}

\RequirePackage{environ}
\RequirePackage{threeparttable}
\RequirePackage{comment}
\RequirePackage{svg}
\RequirePackage[normalem]{ulem}
\RequirePackage{soul}
\RequirePackage{centernot}

\RequirePackage{fancyvrb}
\RequirePackage{fvextra}
\RequirePackage{multicol}
\RequirePackage{tabularx}
\RequirePackage{booktabs}
\RequirePackage{multirow}
\RequirePackage{graphicx}
\RequirePackage{appendixnumberbeamer}
\RequirePackage{subcaption}
\RequirePackage{environ}

% -------------------------------------------------------------------- [ Fonts ]
\RequirePackage{fix-cm}
\RequirePackage{lmodern}
\RequirePackage{gensymb}
\RequirePackage{pifont}
\RequirePackage{fontawesome5}

% ----------------------------------------- [ Math Packages ]

\RequirePackage{fixmath}
\RequirePackage[all,error]{onlyamsmath}
\RequirePackage{mathtools}

% ---------------------------------------- [ Style Packages ]
\RequirePackage{tikz}
\RequirePackage{hyperref}
\RequirePackage[absolute,overlay]{textpos}

\ifgloss{}
  \RequirePackage[nomain,
                  order=word,
                  hyperfirst=false,
                  acronym,
                  shortcuts,
                  nonumberlist]{glossaries}
\fi

\ifbiblio{}
  \RequirePackage[natbib=true,
                  style=alphabetic,
                  url=false,
                  doi=false]{biblatex}
\fi

\ifthenelse{\boolean{stripfonts}}
{}
{%
\RequirePackage[scaled=0.92]{gillius2}
\RequirePackage[small,euler-digits,icomma,OT1,T1%,LY1
           ]{eulervm}
\RequirePackage{inconsolata}
}
%% ---------------------------------------------------------------- [ Commands ]
%%
\newbox\mytempbox{}
\newdimen\mytempdimen{}
\newcommand\includegraphicscopyright[3][]{%
  \leavevmode\vbox{\vskip3pt\raggedright%
    \setbox\mytempbox=\hbox{\includegraphics[#1]{#2}}%
    \mytempdimen=\wd\mytempbox\box\mytempbox\par\vskip1pt%
    \fontsize{3}{3.5}%
    \selectfont{\color{black!70}{\vbox{\hsize=\mytempdimen#3}}}\vskip3pt}}

\newcommand\includegraphicscopyrighturl[3][]
{%
  \href{#3}{\includegraphicscopyright[#1]{#2}{\url{#3}}}
}

\newcommand{\email}[1]{\texttt{\href{mailto:#1}{#1}}}
\newcommand{\www}[1]{\texttt{#1}}

\newcommand{\vfillInfinite}{\vskip0pt plus 1filll}

\graphicspath{{image/},{figure/}}

\DeclareGraphicsExtensions{.pdf,.png,.eps,.gif,.jpg}

\newcommand{\toc}
{%
  \tableofcontents[hidesubsections]
}

\hypersetup{bookmarks=true}

\newcommand{\checkmarkR}{\ensuremath{\reflectbox{\cmark}}}
\newcommand{\cmark}{\text{\ding{51}}}
\newcommand{\xmark}{\text{\ding{55}}}

%% ----------------------------------------------------------------- [ Styling ]

%% Colour Themes

\definecolor{defaultprimary}{RGB/cmyk}{0,56,101/1.0, 0.6, 0.1, 0.53}
\definecolor{defaultexample}{RGB/cmyk}{0,81,51/0.91, 0.14, 0.78, 0.60}
\definecolor{defaultalert}{RGB/cmyk}{125,34,57/0.13, 0.96, 0.26, 0.52}

\csgdef{slidedeckColourPrimary}{defaultprimary}
\csgdef{slidedeckColourAlert}{defaultalert}
\csgdef{slidedeckColourExample}{defaultexample}

\usecolortheme[named=\slidedeckColourPrimary]{structure}
\setbeamercolor{alerted text}{fg=\slidedeckColourAlert}
\setbeamercolor{example text}{fg=\slidedeckColourExample}

%% Custom coloured blocks
\newenvironment<>{colouredblock}[2]
{%
  \begin{actionenv}#3%
    \def\insertblocktitle{#2}%
    \par%
    \mode<presentation>{%
      \setbeamercolor{local structure}{fg=#1, bg=white}
      \setbeamercolor{block title}{fg=white, bg=#1!80!black}
    }%
    \usebeamertemplate{block begin}}
  {%
    \par\usebeamertemplate{block end}%
  \end{actionenv}%
}



%% Better Highlighting
\newcommand{\noticeBFgen}[2]
{%
  \textbf{\textcolor{#1!80!black}{#2}}%
}

\newcommand{\noticeExample}[1]
{%
  \textbf{\textcolor{gla-forest!80!black}{#1}}%
}
\newcommand{\noticeAlert}[1]
{%
  \textbf{\textcolor{gla-burgundy!80!black}{#1}}%
}

\newcommand{\notice}[1]{\structure{#1}}
\newcommand{\bad}[1]{\textcolor{\slidedeckColourAlert}{#1}}
\newcommand{\good}[1]{\textcolor{\slidedeckColourExample}{#1}}

\newcommand{\noticeBF}[1]{\textbf{\structure{#1}}}
\newcommand{\badBF}[1]{\textcolor{\slidedeckColourAlert}{\textbf{#1}}}
\newcommand{\goodBF}[1]{\textcolor{\slidedeckColourExample}{\textbf{#1}}}

%% Better notes for none paused frames.
\NewEnviron{speakerNotePage}{\note{\BODY}}
\NewEnviron{speakerNoteList}{\note[itemize]{\BODY}}


\newcommand{\SlideDeckSectionFrame}[1]
{%
  {%
  \setbeamercolor{background canvas}{bg=\slidedeckColourPrimary}
        \begin{frame}
          \vfill
          \centering
          \usebeamerfont{title}\usebeamercolor[fg]{title in head/foot}\Huge#1\par%
          \vfill
        \end{frame}
  }%
}
%% -- [ Presentation Styling ]

\mode<beamer>
{%

%% Base theme's

  \usetheme{Luebeck}
}

\mode<handout>
{
    % Remove all the styling.
  \usetheme{default}
  \useinnertheme{rectangles}
  \usecolortheme{dove}
  \usefonttheme{structurebold}
  \csgdef{slidedeckColourPrimary}{black}
  \csgdef{slidedeckColourAlert}{black}
  \csgdef{slidedeckColourExample}{black}

}

\mode<beamer|handout>
{
    \useoutertheme{infolines}
}

%% Title styling

\mode<beamer|handout>
{

  % infolines/Luebeck has too tall a title, copy smoothbars
  \setbeamertemplate{frametitle}
  {%
    \usebeamerfont{headline}%
    \nointerlineskip%
    \begin{beamercolorbox}[wd=\paperwidth,leftskip=.3cm,rightskip=.3cm plus1fil,vmode]{frametitle}
      \vskip0.5ex%
      \usebeamerfont*{frametitle}\strut\insertframetitle%
      \ifx\insertframesubtitle\@empty%
        \strut\par%
      \else
        \par{\usebeamerfont*{framesubtitle}{\usebeamercolor[fg]{framesubtitle}\strut\insertframesubtitle}\strut\par}%
      \fi%%
      \usebeamerfont{headline}%
      \vskip0.05ex%
    \end{beamercolorbox}%
  }

}

%% Headline Styling.

\mode<beamer>
{
  \ifthenelse{\boolean{navigation}}
  {%
    %% Header => VFILL | Section if not talking head
    %%       => Section | VFILL if talking head

    \setbeamertemplate{headline}
    {\leavevmode%
      \begin{beamercolorbox}
        [wd=\paperwidth,ht=2.25ex,dp=1.125ex]
        {section in head/foot}%
        \ifthenelse{\boolean{talkinghead}}
        {\insertsectionnavigationhorizontal
          {\paperwidth}
          {}
          {\hskip1pt plus1filll}}
        {\insertsectionnavigationhorizontal
          {\paperwidth}
          {\hskip1pt plus1filll}
          {}}
      \end{beamercolorbox}}
  }{%
    \setbeamertemplate{headline}{}
  }
}

%% Uncoloured Header => VFILL | Section
\mode<handout>
{%
  \ifthenelse{\boolean{navigation}}
  {%
    \setbeamertemplate{headline}
    {\leavevmode%
      \insertsectionnavigationhorizontal
      {\paperwidth}
      {\hskip1pt plus1filll}
      {}
    }
  }{}
}

%% Section Pages
%
\mode<beamer>
{

  \ifthenelse{\boolean{sectionpages}}
  {%
    \AtBeginSection[]
    {%
      \SlideDeckSectionFrame{\insertsection}
    }
  }
}%%

%% Footer styling

\mode<beamer|handout>
{%

  \ifthenelse{\boolean{infofoot}}
  {%
    %% Info Footer => Title | Author | Progress
    \setbeamertemplate{footline}
    {%
      \begin{beamercolorbox}
        [ ht=2.5ex,dp=1.125ex
        ,leftskip=.3cm
        ,rightskip=.3cm plus1fil
        ]
        {section in head/foot}%
        \leavevmode{\usebeamerfont{title in head/foot}\insertshorttitle}%
        \hfill%
        {\usebeamerfont{author in head/foot}%
%          \usebeamercolor[fg]{author in head/foot}%
          \insertshortauthor%
        }
        \hfill%
        {
          \ifbeamertemplateempty{page number in head/foot}{}%
          {%
%            \usebeamercolor[fg]{page number in head/foot}%
            \usebeamerfont{page number in head/foot}%
            \usebeamertemplate{page number in head/foot}%
          }
        }%
      \end{beamercolorbox}
    }
  }{%
    %% Plain Footer => Short Date | VFILL| Progress

    \setbeamercolor{myfootline}{fg=black,bg=white}

    \setbeamertemplate{footline}
    {\leavevmode\hbox{%
        \begin{beamercolorbox}%% Short Date
          [wd=.2\paperwidth,ht=2.25ex,dp=1ex,left]
          {myfootline}%%
          \hspace*{2ex}
          \usebeamerfont{date in head/foot}%
          \insertshortdate{}
        \end{beamercolorbox}%
        \begin{beamercolorbox} %% VFILL
          [wd=0.7\paperwidth,ht=2.25ex,dp=1ex,center]
          {myfootline}
        \end{beamercolorbox}%
        \begin{beamercolorbox}%% Progress
          [wd=0.1\paperwidth, ht=2.25ex, dp=1ex, center]
          {myfootline}%
          \insertframenumber{}/\inserttotalframenumber
        \end{beamercolorbox}}\vskip0pt%
    }
  }
} %%

\mode<beamer|handout>
{
  \setbeamertemplate{navigation symbols}{}
  \setbeamertemplate{itemize items}[rectangle]
  \setbeamertemplate{enumerate items}[rectangle]
  \setbeamertemplate{sections/subsections in toc}[rectangle]
}

% ---------------------------------------------------- [ Styling Speaker notes ]

%% When we are presenting.
\mode<beamer>{

  %% If we have speaker notes then place them at the bottom.
  \ifthenelse{\boolean{speakernotes}}
  {%
    \setbeameroption{show notes on second screen=bottom}
  }{}


  % Make speaker notes easy on the eyes.
  \csgdef{mynote}{yellow!20}
  \setbeamercolor{note page}{bg=\mynote}
  \csgdef{mynote}{yellow!20}
  \setbeamercolor{note title}{bg=\mynote}

  \setbeamertemplate{note page}
  {{%
      \scriptsize
      \usebeamerfont{note title}\usebeamercolor[fg]{note title}%
      \ifbeamercolorempty[bg]{note title}{}
      {%
        \insertvrule{.1\paperheight}{note title.bg}%
        \vskip-.1\paperheight%
        \nointerlineskip%
      }%
      \nointerlineskip
      \vbox to .05\paperheight{\vskip0.5em
        \begin{minipage}[t]{\textwidth}%
          \bfseries%
          \insertsection%
          \xspace%
          \texttt{>}%
          \xspace%
          \insertshortframetitle%
        \end{minipage}}%
    }%
    \ifbeamercolorempty[bg]{note page}{}{%
      \nointerlineskip%
      \insertvrule{.95\paperheight}{note page.bg}%
      \vskip-.95\paperheight%
    }%
    \vskip-.2em
    \nointerlineskip
    \insertnote
  }%

} %%


%% --------------------------------------------------------- [ Handout Styling ]

% When we are producing a handout this means for printing.
\mode<handout>{%

  \setbeamertemplate{note page}[plain]

  \ifthenelse{\boolean{speakernotes}}{
    %% with speaker notes then make it 2 on 1 to show notes.
    \pgfpagesuselayout{2 on 1}[a4paper, border shrink=5mm]
    \setbeameroption{show notes on second screen=bottom}
  }{%
    % otherwise put four to a slide. 4up Handout
    \pgfpagesuselayout{4 on 1}[border shrink=5mm]
  }
}

\endinput

%% [ EOF ]
