#lang racket
(require data/heap)
(require rackunit)

(provide sim? wire?
         (contract-out
          [make-sim        (-> sim?)]
          [sim-wait!       (-> sim? positive? void?)]
          [sim-time        (-> sim? real?)]
          [sim-add-action! (-> positive? (-> any/c) sim? void?)]

          [make-wire       (-> sim? wire?)]
          [wire-on-change! (-> wire? (-> any/c) void?)]
          [wire-value      (-> wire? boolean?)]
          [wire-set!       (-> wire? boolean? void?)]

          [bus-value (-> (listof wire?) natural?)]
          [bus-set!  (-> (listof wire?) natural? void?)]

          [gate-not  (-> wire? wire? void?)]
          [gate-and  (-> wire? wire? wire? void?)]
          [gate-nand (-> wire? wire? wire? void?)]
          [gate-or   (-> wire? wire? wire? void?)]
          [gate-nor  (-> wire? wire? wire? void?)]
          [gate-xor  (-> wire? wire? wire? void?)]

          [wire-not  (-> wire? wire?)]
          [wire-and  (-> wire? wire? wire?)]
          [wire-nand (-> wire? wire? wire?)]
          [wire-or   (-> wire? wire? wire?)]
          [wire-nor  (-> wire? wire? wire?)]
          [wire-xor  (-> wire? wire? wire?)]

          [flip-flop (-> wire? wire? wire? void?)]))

#| Structs |#
(struct sim ([time] [queue])#:mutable)
(struct  wire ([sim] [value] [actions])#:mutable)

#| Symulacja |#
(define (make-sim)
  (sim 0 (make-heap compare)))

(define (compare act1 act2) ;Komparator
  (<= (cdr act1) (cdr act2)))

(define (sim-wait! Simulation Time)
  (set-sim-time! Simulation (+ Time (sim-time Simulation)))
  (do-sim Simulation))

(define (do-sim Simulation)
  (if (= 0 (heap-count (sim-queue Simulation)))
      (void)
      (if (>= (cdr (heap-min (sim-queue Simulation))) (sim-time Simulation))
          (void)
          (begin
            (let ([Act (car (heap-min (sim-queue Simulation)))] [Time (sim-time Simulation)])
              (set-sim-time! Simulation (cdr (heap-min (sim-queue Simulation))))
              (heap-remove-min! (sim-queue Simulation))
              (Act)
              (set-sim-time! Simulation Time)
              (do-sim Simulation))))))

(define (do-actions Actions)
  (if (empty? Actions)
      (void)
      (begin
        ((car Actions))
        (do-actions (cdr Actions)))))

(define (sim-add-action! Delay Act Simulation)
  (heap-add! (sim-queue Simulation) (cons Act (+ Delay (sim-time Simulation)))))

#| Wires |#
(define (make-wire simulation)
  (wire simulation #f  null))

(define (wire-on-change! Wire fun) 
  (set-wire-actions! Wire (cons fun (wire-actions Wire))) (fun))

(define (wire-set! Wire Bool)
  (if (eq? (wire-value Wire) Bool)
      (void)
      (begin
        (set-wire-value! Wire Bool)
        (do-actions (reverse (wire-actions Wire))))))

#| Gates handler |#
(define (wire-binary out in1 in2 Fun Delay) ;fun -> do-op
      (wire-on-change! in1 (λ () (sim-add-action! Delay Fun (wire-sim in1))))
      (wire-on-change! in2 (λ () (sim-add-action! Delay Fun (wire-sim in2)))))

#| Gates |#
(define (gate-not out in)
 (define (do-not) (wire-set! out (not (wire-value in))))
  (wire-on-change! in (λ () (sim-add-action! 1 do-not (wire-sim in)))))  ;;liczby to delay z zadania

(define (gate-and out in1 in2)
  (define (do-and) (wire-set! out (and (wire-value in1) (wire-value in2))))
   (wire-binary out in1 in2 do-and 1))

(define (gate-nand out in1 in2)
  (define (do-nand) (wire-set! out (nand (wire-value in1) (wire-value in2))))
   (wire-binary out in1 in2 do-nand 1))

(define (gate-or out in1 in2)
  (define (do-or) (wire-set! out (or (wire-value in1) (wire-value in2))))
   (wire-binary out in1 in2 do-or 1))

(define (gate-nor out in1 in2)
  (define (do-nor) (wire-set! out (nor (wire-value in1) (wire-value in2))))
   (wire-binary out in1 in2 do-nor 1))

(define (gate-xor out in1 in2)
  (define (do-xor) (wire-set! out (xor (wire-value in1) (wire-value in2))))
   (wire-binary out in1 in2 do-xor 2))

#| Logical wires |#
(define (wire-not in)
  (define return (make-wire (wire-sim in)))
  (begin (gate-not return in) return))

(define (wire-and in1 in2)
  (define return (make-wire (wire-sim in1)))
  (begin (gate-and return in1 in2) return))

(define (wire-nand in1 in2)
  (define return (make-wire (wire-sim in1)))
  (begin (gate-nand return in1 in2) return))

(define (wire-or in1 in2)
 (define return (make-wire (wire-sim in1)))
  (begin (gate-or return in1 in2) return))

(define (wire-nor in1 in2)
  (define return (make-wire (wire-sim in1)))
  (begin (gate-nor return in1 in2) return))

(define (wire-xor in1 in2)
(define return (make-wire (wire-sim in1)))
  (begin (gate-xor return in1 in2) return))

#| Załączony flip-flop |#
(define (flip-flop out clk data)
  (define sim (wire-sim data))
  (define w1  (make-wire sim))
  (define w2  (make-wire sim))
  (define w3  (wire-nand (wire-and w1 clk) w2))
  (gate-nand w1 clk (wire-nand w2 w1))
  (gate-nand w2 w3 data)
  (gate-nand out w1 (wire-nand out w3)))

#| Buses |#
(define (bus-set! wires value)
  (match wires
    ['() (void)]
    [(cons w wires)
     (begin
       (wire-set! w (= (modulo value 2) 1))
       (bus-set! wires (quotient value 2)))]))

(define (bus-value ws)
  (foldr (lambda (w value) (+ (if (wire-value w) 1 0) (* 2 value)))
         0
         ws))