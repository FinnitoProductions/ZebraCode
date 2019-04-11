/*
* Commented by Finn Frankis
* March 16, 2019
* Finds and prints the solution to the Zebra problem using the rule engine by defining a solution rule
* which can only trigger if all of the facts presented in the problem have been asserted. 
*/
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
* stores the house position of the person with this characteristic, which ranges from 1-5 in this given problem. The house
* position must be an integer value.
*/
(deftemplate avh  (slot a)  (slot v)  (slot h (type INTEGER))) 

/*
* Finds the solution to the given problem by requiring a strict pattern of facts which match
* those given in the problem statement. After the solution has been found, asserts a series of facts 
* representing the solution set.
*
* Will only be triggered if all the facts required to satisfy the problem has been asserted; a combination out of 
* the facts asserted must meet each of the requirements, as dictated by the problem statement.
*
* Because there are five houses and each person is of a different nationality, likes a different drink, owns a different 
* pet, and smokes a different type of cigarette, and because each house is of a different color, the pattern-matching
* relies on the assumption (not directly suggested in the problem) that the location of a person with any of these
* characteristics will not be the same as the location of any of the previously-defined ones of the same characteristic.
* For example, the Norwegian man's house location cannot be equal to that of the Japanese man's house location for
* this reason.
*/
(defrule find-solution
  /*
  * Pattern-Matching Variable Definitions:
  * ?n1 - the Englishman's house location
  * ?n2 - the Spaniard's house location
  * ?n3 - the Ukranian's house location
  * ?n4 - the Norwegian's house location
  * ?n5 - the Japanese's house location
  *
  * ?c1 - the red house's location 
  * ?c2 - the ivory house's location
  * ?c3 - the green house's location
  * ?c4 - the yellow house's location
  * ?c5 - the blue house's location
  * 
  * ?p1 - the dog-owner's house location
  * ?p2 - the snail-owner's house location
  * ?p3 - the fox owner's house location
  * ?p4 - the horse-owner's house location
  * ?p5 - the zebra-owner's house location
  *
  * ?d1 - the coffee-drinker's house location
  * ?d2 - the milk-drinker's house location
  * ?d3 - the tea-drinker's house location
  * ?d4 - the orange-juice drinker's house location
  * ?d5 - the water-drinker's house location
  *
  * ?s1 - the Old Golds-smoker's house location
  * ?s2 - the Chesterfield-smoker's house location
  * ?s3 - the Lucky Strikes-smoker's house location
  * ?s4 - the Parliaments-smoker's house location
  * ?s5 - the Kools-smoker's house location
  */

  ; The Englishman lives in the red house.
  /*
  * The Englishman lives at some house location (?n1).
  */
  (avh (a nationality) (v englishman) (h ?n1))
  /*
  * The red house is at some house location (?c1) which is the same as the Englishman's (?n1) because the Englishman lives
  * in the red house.
  */
  (avh (a color) (v red) (h ?c1 & ?n1))


  ; The Spaniard owns the dog.
  /*
  * The Spaniard lives at some house location (?n2) not the same as the Englishman's (?n1).
  */
  (avh (a nationality) (v spaniard) (h ?n2 & ~?n1)) 
  /*
  * The dog-owner lives at some house location (?p1) which is at the same place as the Spaniard's house (?n2) because
  * the Spaniard owns the dog.
  */
  (avh (a pet) (v dog) (h ?p1 & ?n2))


  ; The ivory house is immediately to the left of the green house, where the coffee drinker lives.
  /*
  * The ivory-colored house is at some house location (?c2) not the same as the location of the red house (?c1).
  */
  (avh (a color) (v ivory) (h ?c2&~?c1))
  /*
  * The green-colored house is at some house location (?c3) not the same as the location of the ivory house (?c2) 
  * nor the red house (?c1). Furthermore, the location of the green house is one to the right (one index greater than) 
  * the location of the ivory house (?c2).
  */
  (avh (a color) (v green) (h ?c3&~?c2&~?c1&:(= (+ ?c2 1) ?c3)))
  /*
  * The coffee-drinker lives at some house location (?d1) which is at the same location as the green house (?c3) because
  * the coffee drinker lives in the green house.
  */
  (avh (a drink) (v coffee) (h ?d1&?c3)) 


  ; The milk drinker lives in the middle house.
  /*
  * The milk-drinker lives at some house location (?d2) which is not at the same location as the coffee-drinker's house (?d1) 
  * and is equal to 3 (the middle house index value).
  */
  (avh (a drink) (v milk) (h ?d2&~?d1&3))


  ; The man who smokes Old Golds also keeps snails.
  /*
  * The man who smokes Old Golds lives at some house location (?s1).
  */
  (avh (a smokes) (v old-golds) (h ?s1))
  /*
  * The snails-owner lives at some house location (?p2) at a different location to the dog-owner's house (?p1) but at the
  * same location as that of the Old Golds-smoker (?s1) because the Old Golds-smoker owns snails.
  */
  (avh (a pet) (v snails) (h ?p2&~?p1&?s1)) 


  ; The Ukrainian drinks tea.
  /*
  * The Ukranian lives at some house location (?n3) not the same as the Spaniard's (?n2) nor the Englishman's (?n1).
  */
  (avh (a nationality) (v ukrainian) (h ?n3&~?n2&~?n1))
  /*
  * The tea-drinker lives at some house location (?d3) not the same as the house of the milk-drinker (?d2) or
  * the house of the coffee-drinker (?d1). It is at the same location as that of the Ukranian (?n3) because 
  * the Ukranian drinks tea.
  */
  (avh (a drink) (v tea) (h ?d3&~?d2&~?d1&?n3))


  ; The Norwegian resides in the first house on the left.
  /*
  * The Norwegian lives in the first house (?n4, index 1), which is not the same as the Ukranian's (?n3), the Spaniard's (?n2),
  * nor the Englishman's (?n1).
  */
  (avh (a nationality) (v norwegian) (h ?n4&~?n3&~?n2&~?n1&1)) 


  ; Chesterfields smoker lives next door to the fox owner.
  /*
  * The Chesterfields-smoker lives at some house location (?s2) not the same as the location
  * of the Old Golds-smoker (?s1).
  */
  (avh (a smokes) (v chesterfields) (h ?s2&~?s1))
  /*
  * The fox-owner lives at some house location (?p3) which is not the same as the location of the snail-owner's house 
  * (?p2) nor the dog-owner's house (?p1). Furthermore, because the fox-owner's house is next door to the Chesterfield-smoker's 
  * house (?s2), the Chesterfield-smoker's house is either one house to the left of (one index less than) the fox-owner's
  * house, or one house to the right of (one index greater than) the fox-owner's house.
  */
  (avh (a pet) (v fox) (h ?p3&~?p2&~?p1&:(or (= ?s2 (- ?p3 1)) (= ?s2 (+ ?p3 1)))))


  ; The Lucky Strike smoker drinks orange juice.
  /*
  * The Lucky Strike-smoker lives at some unknown house location (?s3) not the same as the location
  * of the Chesterfield-smoker (?s2) or Old Golds-smoker (?s1).
  */
  (avh (a smokes) (v lucky-strikes) (h ?s3&~?s2&~?s1))
  /*
  * The orange juice-drinker lives at some house location (?d4) not the same as the location of 
  * the tea-drinker (?d3), the milk-drinker (?d2), nor the coffee-drinker (?d1).
  * Furthermore, the orange juice-drinker lives at the same house location as the Lucky Strike-smoker (?s3) because the 
  * Lucky Strike smoker drinks orange juice.
  */
  (avh (a drink) (v orange-juice) (h ?d4&~?d3&~?d2&~?d1&?s3))


  ; The Japanese smokes Parliaments
  /*
  * The Japanese lives at some house location (?n5) not the same as that of the Norwegian's (?n4), 
  * the Ukranian's (?n3), the Spaniard's (?n2), nor the Englishman's (?n1).
  */
  (avh (a nationality) (v japanese) (h ?n5&~?n4&~?n3&~?n2&~?n1))
  /*
  * The Parliaments-smoker lives at some house location (?s4) not the same as that of the Lucky Strike-smoker (?s3),
  * the Chesterfield-smoker (?s2), nor the Old Golds smoker (?s1). Furthermore, this location is the same as that of the
  * Japanese because the Japanese man smokes Parliaments.
  */
  (avh (a smokes) (v parliaments) (h ?s4&~?s3&~?s2&~?s1&?n5))


  ; The horse owner lives next to the Kools smoker, whose house is yellow.
  /*
  * The horse-owner lives at some house location (?p4) which is not the same as the location of the fox-owner's house (?p3),
  * the snail-owner's house (?p2), nor the dog-owner's house (?p1).
  */
  (avh (a pet) (v horse) (h ?p4&~?p3&~?p2&~?p1))
  /*
  * The Kools-smoker lives at some house location (?p5) not the same as that of the Parliaments smoker (?p4), 
  * the Lucky Strike-smoker (?s3), the Chesterfield-smoker (?s2), nor the Old Golds smoker (?s1).
  * Furthermore, because the Kools owner's house is next door to the horse-owner's house (?p2), the 
  * horse-owner's house is either one house to the left of (one index less than) the Kools-smoker's
  * house, or one house to the right of (one index greater than) the Kools-smoker's house.
  */
  (avh (a smokes) (v kools) (h ?s5&~?s4&~?s3&~?s2&~?s1&:(or (= ?p4 (- ?s5 1)) (= ?p4 (+ ?s5 1)))))
  /*
  * The yellow house is at some house location (?c4) which is not the same as the green house (?c3), the ivory house (?c2),
  * nor the red house (?c1). However, the yellow house's location is the same as that of the Kools-smoker's house (?s5) because
  * the Kools smoker lives in a yellow house.
  */
  (avh (a color) (v yellow) (h ?c4&~?c3&~?c2&~?c1&?s5))


  ; The Norwegian lives next to the blue house.
  /*
  * The blue house is at some house location (?c5) which is not the same as that of the yellow house (?c4), the green house (?c3), 
  * the ivory house (?c2), nor the red house (?c1). Also, the blue house is either one to the left or one to to the right of the
  * Norwegian's house (?n4) because the Norwegian lives next to the blue house.
  */
  (avh (a color) (v blue) (h ?c5&~?c4&~?c3&~?c2&~?c1&:(or (= ?c5 (- ?n4 1)) (= ?c5 (+ ?n4 1)))))
  
  ; Who drinks water?  And Who owns the zebra?
  /*
  * The water-drinker lives at some house location (?d5) which is not the same as that of the orange juice-drinker (?d4), 
  * the tea-drinker (?d3), the milk-drinker (?d2), nor the coffee-drinker (?d1).
  */
  (avh (a drink) (v water) (h ?d5&~?d4&~?d3&~?d2&~?d1))
  /*
  * The zebra-owner lives at some house location (?p5) which is not the same as the location of the horse-owner's house (?p4),
  * the fox-owner's house (?p3), the snail-owner's house (?p2), nor the dog-owner's house (?p1).
  */
  (avh (a pet) (v zebra) (h ?p5&~?p4&~?p3&~?p2&~?p1))
  => 
  /*
  * Asserts the solution set to the problem because this call only triggers when all the condtions above have
  * been met, the values stored in each of the variables will each correspond to their solution value.
  */
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
  * Stores each of the solution facts into variables in their correct order so that the solution
  * can be printed later. Note that the following variables are not the same as those stored in the 
  * previous rule (find-solution), but instead are ordered by house location.
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
           ?f15 ?f16 ?f17 ?f18 ?f19 ?f20 ?f21 ?f22 ?f23 ?f24 ?f25) ; retracts all the solution facts previously asserted to clear out the fact-base - unclear why this line is necessary
  /*
  * Prints the solution set to the problem in a convenient table format.
  */
  (printout t "HOUSE | Nationality Color Pet Drink Smokes" crlf)
  (printout t "--------------------------------------------------------------------" crlf)
  (printout t "  1   |" ?n1 " " ?c1 " " ?p1 " " ?d1 " " ?s1 crlf)
  (printout t "  2   |" ?n2 " " ?c2 " " ?p2 " " ?d2 " " ?s2 crlf)
  (printout t "  3   |" ?n3 " " ?c3 " " ?p3 " " ?d3 " " ?s3 crlf)
  (printout t "  4   |" ?n4 " " ?c4 " " ?p4 " " ?d4 " " ?s4 crlf)
  (printout t "  5   |" ?n5 " " ?c5 " " ?p5 " " ?d5 " " ?s5 crlf)
  (printout t crlf crlf))

/*
* Triggers from the initial fact (requires a (reset)) and prints the initial problem statement, carefully explaining
* each fact required to solve the problem. After printing the problem statement, asserts all possible
* values for house color, nationality, pet, drink, and cigarette type. 
*/ 
(defrule startup
   =>
   /*
   * Introduces the user to the problem statement.
   */
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
   /*
   * Asserts each possible value for color, nationality, pet, drink, and cigarette type. Each assertion will trigger 
   * the generate-combinations rule, which will fit the given type of fact and its value into the above avh
   * template with each of the five house positions to ensure the find-solution rule will have a solution 
   * incorporating all possible permutations.
   */
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
* value of that fact type has been asserted, generates all possible combinations for that fact by pairing each piece
* of information with all possible house locations, fitting into the above-defined avh template.
*
* After all possible values for each fact type have been asserted, this rule will have ensured that
* all of those values have been corresponding to all possible house positions to guarantee
* that there will be a permutation of facts to trigger the find-solution rule.
*/
(defrule generate-combinations
   ?f <- (value ?s ?e) ; stores the fact into a value so it can be later retracted
   =>
   (retract ?f) ; retracts the fact after it has been used 
   /* 
   * Asserts the given piece of information with all possible house locations to ultimately generate all permutations.
   */
   (assert (avh (a ?s) (v ?e) (h 1))
           (avh (a ?s) (v ?e) (h 2))
           (avh (a ?s) (v ?e) (h 3))
           (avh (a ?s) (v ?e) (h 4))
           (avh (a ?s) (v ?e) (h 5))))



(defglobal ?*time* = (time)) ; stores the current system time in a variable
(set-reset-globals FALSE) ; prevents a call to "reset" from clearing out global variables to ensure the *time* variable is not lost

/*
* Runs the rule engine a given number of times, resetting before each run of the engine.
*/
(deffunction run-n-times (?n)
  (while (> ?n 0) do 
         (reset)
         (run)
         (bind ?n (- ?n 1)))) 

(run-n-times 1) ; runs the program once when the code is executed to solve the problem

(printout t "Elapsed time: " (integer (- (time) ?*time*)) crlf) ; prints how long the rule engine took to run

