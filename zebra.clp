;;;======================================================
;;;   Who Drinks Water? And Who owns the Zebra?
;;;     
;;;     Another puzzle problem in which there are five 
;;;     houses, each of a different color, inhabited by 
;;;     men of different nationalities, with different 
;;;     pets, drinks, and cigarettes. Given the initial
;;;     set of conditions, it must be determined which
;;;     attributes are assigned to each man.
;;;
;;;     Jess version 4.1 example
;;;
;;;     To execute, merely load, reset and run.
;;;======================================================

;(set-node-index-hash 13)
    
/*
* A template which, in "a," stores the type of fact to be asserted (either house color, nationality, pet, drink, 
* or cigarette type), in "v," stores the value corresponding to that fact type (like a specific house color (ex: red), 
* nationality (ex: englishman), pet (ex: dog), drink (ex: milk), or cigarette type (ex: old-golds)), and in "h"
* stores the house location of the person with this characteristic.
*/
(deftemplate avh  (slot a)  (slot v)  (slot h (type INTEGER))) 

/* 
* Finds the solution to the given problem by requiring a strict pattern of facts which match
* those given in the problem statement. After the solution has been found, asserts a series of facts 
* representing the solution set.
*
* Will be added to the agenda for each assertion by the generate-combinations rule, but will only trigger if the 
* combinations currently asserted satisfies all requirements.
*/
(defrule find-solution
  ; The Englishman lives in the red house.

  (avh (a nationality) (v englishman) (h ?n1)) ; The Englishman lives in some unknown house position.
  (avh (a color) (v red) (h ?c1 & ?n1)) ; The red house's position is the same as the Englishman's.

  ; The Spaniard owns the dog.

  (avh (a nationality) (v spaniard) (h ?n2 & ~?n1)) ; The Spaniard lives in an unknown house not the same as the Englishman's.
  (avh (a pet) (v dog) (h ?p1 & ?n2)) ; The house with the dog has the same number as the Spaniard's.

  ; The ivory house is immediately to the left of the green house,
  ; where the coffee drinker lives.

  (avh (a color) (v ivory) (h ?c2&~?c1))
  (avh (a color) (v green) (h ?c3&~?c2&~?c1&:(= (+ ?c2 1) ?c3)))
  (avh (a drink) (v coffee) (h ?d1&?c3))

  ; The milk drinker lives in the middle house.

  (avh (a drink) (v milk) (h ?d2&~?d1&3))

  ; The man who smokes Old Golds also keeps snails.

  (avh (a smokes) (v old-golds) (h ?s1))
  (avh (a pet) (v snails) (h ?p2&~?p1&?s1))

  ; The Ukrainian drinks tea.

  (avh (a nationality) (v ukrainian) (h ?n3&~?n2&~?n1)) ; The Ukranian lives in some unknown house not the same as the Englishman's or the Spaniard's.
  (avh (a drink) (v tea) (h ?d3&~?d2&~?d1&?n3))

  ; The Norwegian resides in the first house on the left.

  (avh (a nationality) (v norwegian) (h ?n4&~?n3&~?n2&~?n1&1)) ; The Norwegian lives in the first house, which is not the Englishman's, the Spaniard's, or the Ukranian's.

  ; Chesterslots smoker lives next door to the fox owner.

  (avh (a smokes) (v chesterfields) (h ?s2&~?s1))
  (avh (a pet) (v fox) (h ?p3&~?p2&~?p1&:(or (= ?s2 (- ?p3 1)) (= ?s2 (+ ?p3 1)))))

  ; The Lucky Strike smoker drinks orange juice.

  (avh (a smokes) (v lucky-strikes) (h ?s3&~?s2&~?s1))
  (avh (a drink) (v orange-juice) (h ?d4&~?d3&~?d2&~?d1&?s3)) 

  ; The Japanese smokes Parliaments

  (avh (a nationality) (v japanese) (h ?n5&~?n4&~?n3&~?n2&~?n1)) ; The Japanese lives in some unknown house not the same as any of the previous four nationalities.
  (avh (a smokes) (v parliaments) (h ?s4&~?s3&~?s2&~?s1&?n5))

  ; The horse owner lives next to the Kools smoker, 
  ; whose house is yellow.

  (avh (a pet) (v horse) (h ?p4&~?p3&~?p2&~?p1))
  (avh (a smokes) (v kools) (h ?s5&~?s4&~?s3&~?s2&~?s1&:(or (= ?p4 (- ?s5 1)) (= ?p4 (+ ?s5 1)))))
  (avh (a color) (v yellow) (h ?c4&~?c3&~?c2&~?c1&?s5))

  ; The Norwegian lives next to the blue house.

  (avh (a color) (v blue) (h ?c5&~?c4&~?c3&~?c2&~?c1&:(or (= ?c5 (- ?n4 1)) (= ?c5 (+ ?n4 1)))))
  
  ; Who drinks water?  And Who owns the zebra?

  (avh (a drink) (v water) (h ?d5&~?d4&~?d3&~?d2&~?d1))
  (avh (a pet) (v zebra) (h ?p5&~?p4&~?p3&~?p2&~?p1))

  => 
  (assert (solution nationality englishman ?n1)
          (solution color red ?c1)
          (solution nationality spaniard ?n2)
          (solution pet dog ?p1)
          (solution color ivory ?c2)
          (solution color green ?c3)
          (solution drink coffee ?d1)
          (solution drink milk ?d2) 
          (solution smokes old-golds ?s1)
          (solution pet snails ?p2)
          (solution nationality ukrainian ?n3)
          (solution drink tea ?d3)
          (solution nationality norwegian ?n4)
          (solution smokes chesterfields ?s2)
          (solution pet fox ?p3)
          (solution smokes lucky-strikes ?s3)
          (solution drink orange-juice ?d4) 
          (solution nationality japanese ?n5)
          (solution smokes parliaments ?s4)
          (solution pet horse ?p4) 
          (solution smokes kools ?s5)
          (solution color yellow ?c4)
          (solution color blue ?c5)
          (solution drink water ?d5)
          (solution pet zebra ?p5))
  )

/*
* Prints out the solution to the Zebra problem by storing all the facts asserted by the
* find-solution rule and retracting each one to clear out the rule engine, then printing
* the solution set for each nationality's corresponding house color, pet, preferred drink,
* and cigarette type.
*/
(defrule print-solution
  /*
  * Stores each of the solution facts into the variables in their correct order.
  */
  ?f1 <- (solution nationality ?n1 1)
  ?f2 <- (solution color ?c1 1)
  ?f3 <- (solution pet ?p1 1)
  ?f4 <- (solution drink ?d1 1)
  ?f5 <- (solution smokes ?s1 1)
  ?f6 <- (solution nationality ?n2 2)
  ?f7 <- (solution color ?c2 2)
  ?f8 <- (solution pet ?p2 2)
  ?f9 <- (solution drink ?d2 2)
  ?f10 <- (solution smokes ?s2 2)
  ?f11 <- (solution nationality ?n3 3)
  ?f12 <- (solution color ?c3 3)
  ?f13 <- (solution pet ?p3 3)
  ?f14 <- (solution drink ?d3 3)
  ?f15 <- (solution smokes ?s3 3)
  ?f16 <- (solution nationality ?n4 4)
  ?f17 <- (solution color ?c4 4)
  ?f18 <- (solution pet ?p4 4)
  ?f19 <- (solution drink ?d4 4)
  ?f20 <- (solution smokes ?s4 4)
  ?f21 <- (solution nationality ?n5 5)
  ?f22 <- (solution color ?c5 5)
  ?f23 <- (solution pet ?p5 5)
  ?f24 <- (solution drink ?d5 5)
  ?f25 <- (solution smokes ?s5 5)
  =>
  (retract ?f1 ?f2 ?f3 ?f4 ?f5 ?f6 ?f7 ?f8 ?f9 ?f10 ?f11 ?f12 ?f13 ?f14
           ?f15 ?f16 ?f17 ?f18 ?f19 ?f20 ?f21 ?f22 ?f23 ?f24 ?f25) ; retracts all the solution facts previously asserted
  (printout t "HOUSE | Nationality Color Pet Drink Smokes" crlf)
  (printout t "--------------------------------------------------------------------" crlf)
  (printout t "  1   |" ?n1 " " ?c1 " " ?p1 " " ?d1 " " ?s1 crlf)
  (printout t "  2   |" ?n2 " " ?c2 " " ?p2 " " ?d2 " " ?s2 crlf)
  (printout t "  3   |" ?n3 " " ?c3 " " ?p3 " " ?d3 " " ?s3 crlf)
  (printout t "  4   |" ?n4 " " ?c4 " " ?p4 " " ?d4 " " ?s4 crlf)
  (printout t "  5   |" ?n5 " " ?c5 " " ?p5 " " ?d5 " " ?s5 crlf)
  (printout t crlf crlf))

/*
* Triggers from the initial fact and prints the initial problem statement, carefully explaining
* each fact required to solve the problem. After printing the problem statement, asserts all possible
* values for house color, nationality, pet, drink, and cigarette type. Each assertion will trigger 
* the generate-combinations rule, which will place asser
*/ 
(defrule startup
   =>
   (printout t
    "There are five houses, each of a different color, inhabited by men of"  crlf
    "different nationalities, with different pets, drinks, and cigarettes."  crlf
    crlf
    "The Englishman lives in the red house.  The Spaniard owns the dog."     crlf
    "The ivory house is immediately to the left of the green house, where"   crlf
    "the coffee drinker lives.  The milk drinker lives in the middle house." crlf
    "The man who smokes Old Golds also keeps snails.  The Ukrainian drinks"  crlf
    "tea.  The Norwegian resides in the first house on the left.  The"       crlf)
   (printout t
    "Chesterfields smoker lives next door to the fox owner.  The Lucky"      crlf
    "Strike smoker drinks orange juice.  The Japanese smokes Parliaments."   crlf
    "The horse owner lives next to the Kools smoker, whose house is yellow." crlf
    "The Norwegian lives next to the blue house."			     crlf
    crlf
    "Now, who drinks water?  And who owns the zebra?" crlf crlf)
   (assert (value color red) 
           (value color green) 
           (value color ivory)
           (value color yellow)
           (value color blue)
           (value nationality englishman)
           (value nationality spaniard)
           (value nationality ukrainian) 
           (value nationality norwegian)
           (value nationality japanese)
           (value pet dog)
           (value pet snails)
           (value pet fox)
           (value pet horse)
           (value pet zebra)
           (value drink water)
           (value drink coffee)
           (value drink milk)
           (value drink orange-juice)
           (value drink tea)
           (value smokes old-golds)
           (value smokes kools)
           (value smokes chesterfields)
           (value smokes lucky-strikes)
           (value smokes parliaments)) 
   )

/*
* After a fact representing a given fact type (house color, nationality, preferred drink, pet, or cigarette type) and 
* value for that fact type has been asserted, generates all possible combinations for that fact by pairing each piece
* of information with a given house position.
*/
(defrule generate-combinations
   ?f <- (value ?s ?e)
   =>
   (retract ?f)
   (assert (avh (a ?s) (v ?e) (h 1))
           (avh (a ?s) (v ?e) (h 2))
           (avh (a ?s) (v ?e) (h 3))
           (avh (a ?s) (v ?e) (h 4))
           (avh (a ?s) (v ?e) (h 5))))



(defglobal ?*time* = (time))
(set-reset-globals FALSE) ; prevents a call to "reset" from clearing out global variables to ensure the *time* variable is not lost

/*
* Runs the rule engine a given number of times, resetting before each call.
*/
(deffunction run-n-times (?n)
  (while (> ?n 0) do
         (reset)
         (run)
         (bind ?n (- ?n 1))))

(run-n-times 1)

(printout t "Elapsed time: " (integer (- (time) ?*time*)) crlf)

