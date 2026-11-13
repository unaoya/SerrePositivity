module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# shifted 因子からの同じ次数の余積

## 概要
shift と ULift による添字変更の後も、元の複体の余積の各次数を同じ脚で記述する。

## 方針
次数評価の余積保存と shift の各次数の同型を用い、逆射を余積の普遍性で作る。

## 規約
次数は任意の整数、添字の ULift の宇宙も指定する。

## 使われ方
HA 1.2.4。bar の各次数の二段の余積の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A] {ι : Type v}
variable [HasCoproducts.{v} (ModuleCat.{u} A)]

/-- 元の余積への包含の前に shift の次数同型を合成した、ULift 添字の余積候補。 -/
def shiftedCoproductDegreeCofan (K : ι → Complex A) [HasCoproduct K] (a q : ℤ) :
    Cofan (fun s : ULift.{w} ι => ((K s.down)⟦a⟧).X q) :=
  Cofan.mk ((∐ K).X (q + a)) (fun s =>
    ((K s.down).shiftFunctorObjXIso a q (q + a) rfl).hom ≫ (Sigma.ι K s.down).f (q + a))

/-- shift と同じ ULift 添字による各次数の余積は、元の包含のまま普遍的。 -/
def shiftedCoproductDegreeCofan_isColimit (K : ι → Complex A) [HasCoproduct K] (a q : ℤ) :
    IsColimit (shiftedCoproductDegreeCofan.{u, v, w} A K a q) := by
  let E := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) (q + a)
  let c₀ := Cofan.mk ((∐ K).X (q + a)) (fun i => (Sigma.ι K i).f (q + a))
  have hc₀ : IsColimit c₀ :=
    isColimitCofanMkObjOfIsColimit E K (Sigma.ι K) (coproductIsCoproduct K)
  refine Cofan.IsColimit.mk _ (fun c => hc₀.desc
    (Cofan.mk c.pt (fun i => ((K i).shiftFunctorObjXIso a q (q + a) rfl).inv ≫
      c.inj (ULift.up i)))) ?_ ?_
  · intro c s
    change (_ ≫ c₀.inj s.down) ≫ _ = _
    apply (Category.assoc _ _ _).trans
    apply (congrArg (fun z => ((K s.down).shiftFunctorObjXIso a q (q + a) rfl).hom ≫ z)
      (Cofan.IsColimit.fac hc₀ _ s.down)).trans
    exact Iso.hom_inv_id_assoc ((K s.down).shiftFunctorObjXIso a q (q + a) rfl) _
  · intro c m hm
    apply Cofan.IsColimit.hom_ext hc₀
    intro i
    apply Eq.trans _ (Cofan.IsColimit.fac hc₀ _ i).symm
    apply (cancel_epi ((K i).shiftFunctorObjXIso a q (q + a) rfl).hom).mp
    have hh := hm (ULift.up i)
    change (((K i).shiftFunctorObjXIso a q (q + a) rfl).hom ≫ c₀.inj i) ≫ m = _ at hh
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hh

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
