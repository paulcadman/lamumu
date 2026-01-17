import Lamumu.Basic
import Lamumu.Binding

namespace Fun

def translate' : Term → Core.Producer
 | .var v => .var v
 | .lit l => .lit l
 | .bin op t1 t2 =>
   let ct1 := translate' t1
   let ct2 := translate' t2
   .mu (.free 0) (.prim op ct1 ct2 (.covar (.bound 0)))
 | .ifz t1 t2 t3 =>
   let ct1 := translate' t1
   let ct2 := translate' t2
   let ct3 := translate' t3
   .mu
     (.free 0)
     (.ifz ct1
           (.cut ct2 (.covar (.bound 0)))
           (.cut ct3 (.covar (.bound 0))))
 | .let x assign body =>
   let cassign := translate' assign
   let cbody := translate' body
   let s := Core.closeVar x (.cut cbody (.covar (.bound 0)))
   .mu (.free 0) (.cut cassign (.mu_tilde x s))

def translate (t : Term) : Core.Statement :=
  let p := translate' t
  .cut p (.covar .star)

end Fun
