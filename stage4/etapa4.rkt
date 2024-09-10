#lang racket
(require "suffix-tree-stream.rkt")
(require "collection.rkt")

(provide (all-defined-out))

;; Vom prelua toate funcțiile din etapele 1-3 (exceptând
;; longest-common-substring, care nu beneficiază de 
;; reprezentarea ca flux întrucât parcurge tot arborele)
;; și le vom adapta la noua reprezentare a unui ST.
;;
;; Pentru că un ST este construit pornind de la o colecție
;; de sufixe și pentru că ne dorim să nu calculăm toate
;; sufixele decât dacă este nevoie, vom modifica toate
;; funcțiile care prelucrau liste de sufixe pentru a
;; prelucra fluxuri de sufixe.
;;
;; Obs: fără această modificare a listelor de sufixe în
;; fluxuri de sufixe, și presupunând că am manipulat
;; arborii de sufixe doar prin interfața definită în
;; fișierul suffix-tree (respectând astfel bariera de 
;; abstractizare), ar trebui să alterăm doar funcția 
;; suffixes->st care este practic un constructor pentru
;; tipul ST.
;; Din cauza transformării listelor de sufixe în fluxuri,
;; avem mult mai multe implementări de modificat.
;; Puteam evita acest lucru? Da, utilizând conceptul de
;; colecție de sufixe de la început (în loc să presupunem
;; că ele vor fi prelucrate ca liste). În loc de cons,
;; car, cdr, map, filter, etc. am fi folosit de fiecare
;; dată collection-cons, collection-first, ... etc. -
;; aceste funcții fiind definite într-o bibliotecă
;; inițială ca fiind echivalentele lor pe liste, și
;; redefinite ulterior în stream-cons, stream-first,
;; ... etc. Operatorii pe colecții de sufixe ar fi 
;; folosit, desigur, doar funcții de tip collection-.
;;
;; Am ales să nu procedăm astfel pentru că ar fi provocat
;; confuzie la momentul respectiv (când chiar operatorii
;; pe liste erau o noutate) și pentru a vă da ocazia să
;; faceți singuri acest "re-design".


; TODO
; Copiați din etapele anterioare implementările funcțiilor
; de mai jos și modificați-le astfel:
; - Toate funcțiile care lucrează cu liste de sufixe vor
;   lucra cu un nou tip de date Collection, ai cărui
;   constructori și operatori vor fi definiți de voi
;   în fișierul collection.rkt.
; - Pentru toate funcțiile, trebuie să vă asigurați că
;   este respectată bariera de abstractizare (atât în 
;   cazul tipului ST cât și în cazul tipului Collection).
; Obs: cu cât mai multe funcții rămân nemodificate, cu atât
; este mai bine (înseamnă că design-ul inițial a fost bun).

(define (prefix word1 word2 lista)
  (if (or (null? word1) (null? word2))
      (list lista word1 word2)
      (if (equal? (car word1) (car word2)) ; verific daca au prefixele la fel
          (prefix (cdr word1) (cdr word2) (append lista (list (car word1))))
          (list lista word1 word2))))

(define (longest-common-prefix w1 w2)
  (prefix w1 w2 '()))

; am schimbat, în numele funcției, cuvântul list în
; cuvântul collection
(define (longest-common-prefix-of-collection words)
  (if (or (= (collection-length words) 1) (= 1 (length (collection-first words))))
      (collection-first words)
      (longest-common-prefix-of-collection (collection-cons (car (prefix (collection-first words) (collection-first (collection-rest words)) '()))
                                                        (collection-rest (collection-rest words))))))

(define (caz1 branch pattern) ; verific sa vad daca patternul se regaseste complet in subarbore
  (equal? (length (car (prefix (car branch) pattern '()))) (length pattern)))

(define (caz2 branch pattern) ; verfic sa vad daca exista o parte din pattern pe 2 ramuri
  (define longest-prefix (longest-common-prefix (car branch) pattern)) ; retin cel mai lung prefix dintre pattern si prima lista din ramura
  (if (null? (cdr branch))
      (list #f (car (longest-common-prefix (car branch) pattern))) ; inseamna ca nu mai exista nimic din pattern intr o alta lista
      #f)) ; inseama ca e fals cazul 2 deci este cazul 3

(define (caz3 branch pattern)
  (define longest-prefix (car (longest-common-prefix (car branch) pattern))) ; cel mai lung prefix
  (define rest (drop pattern (length longest-prefix)))
  (define rest-branch (cdr branch))
  (let* ([x longest-prefix]
         [y rest]
         [z rest-branch])
    (list x y z)))

(define (match-pattern-with-label st pattern) 
  (define branch (get-ch-branch st (car pattern))) ; extrag subarborele/ramura care contine prefixul
  (if (not (pair? branch)) ; verific sa vad daca a fost gasit un subarbore
      (list #f '())
      (if (caz1 branch pattern) 
          #t ; inseamna ca este cazul 1
          (if (caz2 branch pattern)
              (list #f (car (longest-common-prefix (car branch) pattern)))
              (caz3 branch pattern)))))

(define (st-has-pattern? st pattern)
  (let* ([result (match-pattern-with-label st pattern)])
    (cond
      ((equal? result #t) #t)
      ((equal? (collection-first result) #f) #f)
      (else (st-has-pattern? (car (cdr (cdr result))) (car (cdr result)))))))


(define (get-suffixes text) ; face un flux cu sufixele unui test
  (if (null? text)
      '()
      (collection-cons text (get-suffixes (cdr text)))))

(define (get-ch-words words ch) ; word este un flux de cuvinte ; returneaza un flux 
  (collection-filter (lambda (first-ch) (char=? (collection-first first-ch) ch)) words))

(define (ast-func suffixes); returneaza o lista formata din label si flux
  (cons (list (collection-first (collection-first suffixes))) (collection-map (lambda (word) (collection-rest word)) suffixes)))

(define (cst-func suffixes) ; labelul este o lista ; returneaza un flux format dintr o lista (label) si fluxuri (restul cuvintelor)
  (let* ([longest-prefix (longest-common-prefix-of-collection suffixes)]
         [list-suffixes (collection-map (lambda (word) (drop word (length longest-prefix))) suffixes)])
    (cons longest-prefix list-suffixes)))

; considerați că și parametrul alphabet este un flux
; (desigur, și suffixes este un flux, fiind o colecție
; de sufixe)

(define (branch labeling-func list-suffixes alphabet)
  (cond
    [(collection-empty? list-suffixes) empty-st]
    [else (let* ([functie (labeling-func list-suffixes)])
            (cons (car functie) ; construiesc lista dintre prefix si restul de sufixe
                  (suffixes->st labeling-func ; apelez functia suffixes->st cu sufixele ce au ramas
                                (cdr functie)
                                alphabet)))]))

(define (suffixes->st labeling-func suffixes alphabet)
  (collection-filter (lambda (lst) (not (null? lst)))
                 (collection-map (lambda (letter) 
                               (branch labeling-func ; apelez functia branch creata de mine pentru fiecare latura ca sa creez ramura arborelui
                                       (get-ch-words (collection-filter (lambda (s) (not (collection-empty? s))) suffixes)
                                                     letter) ; extrag doar sufixele care incep cu letter
                                       alphabet))
                             alphabet)))


; nu uitați să convertiți alfabetul într-un flux
(define (list-to-stream lst)
  (if (null? lst)
      '()
      (collection-cons (car lst)
                   (list-to-stream (cdr lst)))))

(define (text->st labeling-func) ; fac o functie de tip curry
  (lambda (text)
    (let* ([lista-completa (append text (list #\$))]
           [collection (get-suffixes lista-completa)] ; creez lista cu toate sufixele cuvantului
           [alphabet (sort (remove-duplicates lista-completa) char<?)]) ; creez lista de litere
      (suffixes->st labeling-func collection (list-to-stream alphabet)))))

(define (text->ast text)
  ((text->st ast-func) text))

(define (text->cst text)
  ((text->st cst-func) text))

; dacă ați respectat bariera de abstractizare,
; această funcție va rămâne nemodificată.
(define (substring? text pattern)
  (let ([suffixes-tree (text->ast text)]) ; construiesc st de tip ast
    (st-has-pattern? suffixes-tree pattern))) ; apelez functia st-has-pattern pentru a afla daca se regaseste patternul


; dacă ați respectat bariera de abstractizare,
; această funcție va rămâne nemodificată.
(define (repeated-substring-of-given-length text len)
  (let* ([suffixes-tree (text->cst text)])
    (define (find-substring branch lungime-ramasa)
      (let* ([label (get-branch-label branch)]
             [lungime-label (length label)])
        (cond
          [(member #\$ label) #f]  ; aici trebuie sa verific daca nodul este frunza
          [(<= lungime-ramasa lungime-label) (take label lungime-ramasa)] ; inseamna ca am ajuns la final si construiesc cuvnatul
          [(equal? #f (find (get-branch-subtree branch) (- lungime-ramasa lungime-label))) #f] ; verific daca urmatorul este corect sau nu
          [else (append label (find (get-branch-subtree branch) (- lungime-ramasa lungime-label)))])))
    (define (find st lungime)
      (cond
        [(st-empty? st) #f] ; inseamna ca n am gasit niciun branch corect
        [(equal? #f (find-substring (first-branch st) lungime)) (find (other-branches st) lungime)] ; inseamna ca trebuie sa ma duc pe alt branch
        [else (find-substring (first-branch st) lungime)]))
    (find suffixes-tree len)))