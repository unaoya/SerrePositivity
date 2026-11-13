module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# 有限余積の指定包含射と積の座標

DAG XIII Construction 2.2.6 の有限対角線比較の補助。
［一般圏］基盤への移動候補。同じ有限双積の包含射を、
通常の積の指定座標へ移すと Kronecker の式になる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits
variable {k : Type u} [Ring k] {I : Type} [Finite I] [DecidableEq I]
variable (F : I → ModuleCat.{u} k)

omit [DecidableEq I] in
/-- 既存の双積と通常の積の指定同型は、元の各射影を保つ。 -/
@[reassoc]
lemma finiteBiproductCoordinates_projection (i : I) :
    (ModuleCat.biproductIsoPi F).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      biproduct.π F i :=
  IsLimit.conePointUniqueUpToIso_hom_comp (biproduct.isLimit F)
    (ModuleCat.HasLimit.productLimitCone F).isLimit (Discrete.mk i)

/-- 同じ有限余積の包含射を、通常の積の同じ座標へ送る。 -/
lemma finiteBiproductCoordinates_inclusion (i j : I) (x : F i) :
    (ModuleCat.biproductIsoPi F).hom ((biproduct.ι F i).hom x) j =
      if h : i = j then (eqToHom (congrArg F h)).hom x else 0 := by
  have h := congrArg (fun f => f.hom x)
    (congrArg (fun f => biproduct.ι F i ≫ f)
      (finiteBiproductCoordinates_projection F j))
  change (ModuleCat.biproductIsoPi F).hom.hom ((biproduct.ι F i).hom x) j =
    (biproduct.ι F i ≫ biproduct.π F j).hom x at h
  by_cases hij : i = j
  · subst j
    rw [dite_eq_left rfl]
    change (ModuleCat.biproductIsoPi F).hom.hom ((biproduct.ι F i).hom x) i = x
    simpa only [biproduct.ι_π_self, ModuleCat.hom_id, LinearMap.id_apply] using h
  · rw [dite_eq_right hij]
    change (ModuleCat.biproductIsoPi F).hom.hom ((biproduct.ι F i).hom x) j = 0
    simpa only [biproduct.ι_π_ne _ hij, ModuleCat.hom_zero, LinearMap.zero_apply] using h

end SerrePositivity.EInfinity.PowerOperation
