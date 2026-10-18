module
public import SerrePositivity.KST.ProExcision.NonUnitalHatGL
public import SerrePositivity.KST.Comparison.GLComponents

/-!
# 標準単位化の連結成分の整数射影

概要：非単位単体環の整数単位化の連結成分から整数環への実準同型を構成する。
方針：整数成分は全ての面・退化で不変なので、零次の整数射影を π₀ に降ろす。
規約：KST Claim 4.15、単位化上の ĜL と整数核の比較。
使われ方：π₀ の逆行列を持ち上げたときに整数核条件が保たれることの証明。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial

/-- 概要：単位化の辺の整数成分は両端で等しい。
方針：面写像による整数成分の保存と両端条件を使う。
規約：KST Claim 4.15。使われ方：π₀ への整数射影の降下。 -/
lemma NonUnitalSimplicialRing.fst_edge (I : NonUnitalSimplicialRing.{u})
    {a b : I.standardIdeal.ambient.obj (op ⦋0⦌)}
    (e : (Comparison.ringSpace I.standardIdeal.ambient).Edge a b) : a.fst = b.fst := by
  have hs := congrArg (fun x : Unitization ℤ (I.obj (op ⦋0⦌)) ↦ x.fst) e.src_eq
  have ht := congrArg (fun x : Unitization ℤ (I.obj (op ⦋0⦌)) ↦ x.fst) e.tgt_eq
  change (integerUnitizationMap (I.map (SimplexCategory.δ 1).op) e.edge).fst = a.fst at hs
  change (integerUnitizationMap (I.map (SimplexCategory.δ 0).op) e.edge).fst = b.fst at ht
  rw [integerUnitizationMap_fst] at hs ht
  exact hs.symm.trans ht

/-- 概要：単位化の成分環から整数環への実環準同型。
方針：整数成分を商へ降ろし、環法則を零次の代表で証明する。
規約：KST Claim 4.15。使われ方：π₀ での逆行列の整数核条件。 -/
def NonUnitalSimplicialRing.componentsFst (I : NonUnitalSimplicialRing.{u}) :
    π₀ (Comparison.ringSpace I.standardIdeal.ambient) →+* ℤ where
  toFun := π₀.lift (fun x ↦ x.fst) (fun _ _ e ↦ I.fst_edge e)
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    exact Unitization.fst_add a b
  map_mul' a b := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    exact Unitization.fst_mul a b

/-- 概要：成分行列の整数射影は元の行列の整数射影に等しい。
方針：零次成分写像の各成分を代表で計算する。
規約：KST Claim 4.15。使われ方：成分環での積の等式の整数行列への移送。 -/
lemma NonUnitalSimplicialRing.componentsFst_matrix (I : NonUnitalSimplicialRing.{u})
    (n : ℕ) (A : Matrix (Fin n) (Fin n) (I.standardIdeal.ambient.obj (op ⦋0⦌))) :
    I.componentsFst.mapMatrix (Comparison.matrixToComponents I.standardIdeal.ambient n 0 A) =
      (Unitization.fstHom ℤ (I.obj (op ⦋0⦌))).mapMatrix A := by
  apply Matrix.ext
  intro i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply,
    Comparison.matrixToComponents_zero_entry]
  rfl

end SerrePositivity.KST.ProExcision
