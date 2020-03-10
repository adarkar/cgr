# cgr

Uno strumento per rendere visibile l'esecuzione di programmi C (o quasi, per ora).

## Motivazioni

L'esperienza nell'insegnamento mi ha portato a cercare di comprendere dove gli studenti hanno maggiori difficoltà nello studio dell'informatica.

Fondamentale è, per lo studente di informatica, comprendere bene la distinzione tra il codice (statico) e l'esecuzione (dinamica) di una macchina calcolatrice descritta da quel codice.
Spesso si assiste però a una grande confusione tra questi due aspetti.
Lo studente fatica dunque nei fondamenti della materia e presto si scoraggia per via dei fallimenti.

Un modo per cercare di aiutare la comprensione è quello di rendere visibile effettivamente ciò che è normalmente nascosto e visibile solo con gli occhi della mente.
Questo vale per qualunque disciplina, ovviamente.
Rendere esplicito e visibile ciò che non lo è in partenza è uno dei criteri imprescindibili con cui si caratterizza un insegnamento efficace.

Si assiste inoltre ad alcuni sfortunati accidenti storici che rendono ancora più difficoltoso l'apprendimento dell'informatica, molto più di quello che già è per sua natura intrinseca.

* L'uso del linguaggio C.
* La mancanza di una progressione didattica dal semplice al complesso.
* La mancata spiegazione della semantica del codice.

Lo strumento consente di osservare in modo visivo ed esplicito proprio quella semantica che dovrebbe essere oggetto degli insegnamenti ma che è purtroppo spesso trascurata.

La pratica ripetuta dell'osservazione dei meccanismi interni ad una macchina calcolatrice automatica facilita l'interiorizzazione di quei meccanismi, consentendo allo studente di fare propria la semantica e poterla gestire anche quando rimarrà accessibile solo per mezzo della mente attraverso il codice.

Anche lo studente più avanzato può trarre giovamento dallo strumento, avendo accesso a possibilità di riflessioni più complesse.

## Una didattica efficace

Lo studente che fosse mosso da grande desiderio di apprendimento può trovare una didattica efficace nel bellissimo libro [HTDP](https://htdp.org/2019-02-24/part_preface.html).
Sviluppato con serietà e dedizione dagli autori, usa un linguaggio appositamente studiato per la didattica (in contrapposizione ad un linguaggio per esperti come il C), gli argomenti sono perfettamente ordinati partendo dai concetti più semplici (in contrapposizione a presentazioni precoci e disorganiche di concetti complessi).

Si osserva in quel libro una abilità pedagogica veramente eccezionale.
Soprattutto, consente di apprendere i principi dell'informatica anche a quegli studenti che prenderanno poi strade diverse e non incontreranno più i dettagli della nostra disciplina.

Per chi rimane costretto ad imparare usando il C, spero che questo strumento possa accendere qualche possibilità di riflessione e fornire un sostegno soprattutto a quegli studenti dalle grandi potenzialità così sfortunatamente sprecate da una didattica raffazzonata e mal gestita che produce noia e frustrazione spegnendo la vivacità mentale invece di accenderla.

A scanso di equivoci, ricordiamo che il C è un linguaggio splendido, con una sua eleganza decisamente poco comune.
È ovviamente un linguaggio storicamente importante ed è un linguaggio ottimamente progettato per i suoi scopi.

Il problema sono proprio i suoi scopi: la realizzazione sistemi di basso livello da parte di utenti oltremodo esperti.
In pratica scopi diametralmente opposti a quelli di uno studente alle prime armi.

## Istruzioni per l'uso

* Scaricare il file dalle release, link diretto:
[cgr.html](https://github.com/adarkar/cgr/releases/download/v0.1/cgr.html)
* Aprire con un browser

## Build

Sperando che sia corretto:
```
npm i -g purescript
npm i -g spago
npm i -g parcel
npm run build
```
