module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

/-!
概要：端点の表示が異なる同じ全経路の affine 合成を比較し、前合成の保存を証明する。
方針：経路評価から中点の等式を取り出し、元の affine 線形式を使う。
規約：経路の一致を明示入力する。使われ方：元の輪郭と affine 二自然性の合成の同定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {B W T : Mon (Complex R)} {N : Bimod B B}
  {q q' : W ⟶ B} {a b c a' b' c' : W ⟶ algebra B N}
  {v : RelativeWitness q N a b} {w : RelativeWitness q N b c}
  {v' : RelativeWitness q' N a' b'} {w' : RelativeWitness q' N b' c'}

lemma comp_congr_hom_of_paths (hv : v.hom = v'.hom) (hw : w.hom = w'.hom) :
    (v.comp w).hom = (v'.comp w').hom := by
  have hb : b = b' := v.target_eq.symm.trans
    ((congrArg (fun k => k ≫ DGAlgebra.Path.target R (algebra B N)) hv).trans v'.target_eq)
  apply Mon.Hom.ext
  rw [comp_hom_linear, comp_hom_linear, hv, hw, hb]

/-- 証明済みの全射の等式で、元の端点・底を保って経路表示だけを移す。 -/
def replaceHom (v : RelativeWitness q N a b)
    (k : W ⟶ DGAlgebra.Path.algebra R (algebra B N)) (hk : v.hom = k) :
    RelativeWitness q N a b where
  hom := k
  source_eq := (congrArg (fun t => t ≫ DGAlgebra.Path.source R (algebra B N)) hk).symm.trans
    v.source_eq
  target_eq := (congrArg (fun t => t ≫ DGAlgebra.Path.target R (algebra B N)) hk).symm.trans
    v.target_eq
  projection_eq := (congrArg (fun t => t ≫ DGAlgebra.Path.map R (projection B N)) hk).symm.trans
    v.projection_eq

lemma precomp_comp_hom (v : RelativeWitness q N a b) (w : RelativeWitness q N b c)
    (e : T ⟶ W) : ((v.comp w).precomp e).hom =
      ((v.precomp e).comp (w.precomp e)).hom := by
  apply Mon.Hom.ext
  change (e ≫ (v.comp w).hom).hom = _
  rw [Mon.comp_hom', comp_hom_linear, comp_hom_linear]
  simp only [comp_add, comp_sub, ← Mon.comp_hom', Category.assoc]
  rfl

lemma replaceHom_comp_hom (v : RelativeWitness q N a b) (w : RelativeWitness q N b c)
    (k : W ⟶ DGAlgebra.Path.algebra R (algebra B N)) (hk : v.hom = k) :
    ((v.replaceHom k hk).comp w).hom = (v.comp w).hom :=
  comp_congr_hom_of_paths hk.symm rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
