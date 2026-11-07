module

public import SerrePositivity.HomologicalAlgebra.Cech.Basic
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Comma

/-!
概要：増大 Čech 完全性の filtered 余極限による保存。
方針：各次数で環から加法群への忘却が filtered 余極限を保ち、加法群では filtered 余極限が完全であることを使う。
規約：環と図式の添字は同じ宇宙に取る。
使われ方：有限表示の模型から任意の完全代数へ移るときの Čech 完全性。
-/

@[expose] public section
noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

namespace SerrePositivity.Cech

set_option backward.isDefEq.respectTransparency false

variable {J : Type u} [SmallCategory J] [IsFiltered J]

private def degree (n : ℕ) : AugmentedSimplexCategory :=
  match n with
  | 0 => .star
  | k + 1 => .of ⦋k⦌

private theorem ringCochain_preserves :
    PreservesColimitsOfShape J ringCochain.{u} := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let F := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.inverse ⋙
    (evaluation AugmentedSimplexCategory CommRingCat).obj (degree n) ⋙ ringToAb
  let : PreservesFilteredColimits ringToAb.{u} :=
    comp_preservesFilteredColimits _ _
  have : PreservesColimitsOfShape J F := by dsimp [F]; infer_instance
  apply preservesColimitsOfShape_of_natIso (F := F)
  cases n <;> exact NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp; rfl)

/-- filtered 余極限は加法群の完全な増大余鎖複体を完全な複体に送る。 -/
private theorem acyclic_colimit (F : J ⥤ CochainComplex AddCommGrpCat.{u} ℕ)
    (h : ∀ j, (F.obj j).Acyclic) : (colimit F).Acyclic := by
  intro n
  let p := (ComplexShape.up ℕ).prev n
  let q := (ComplexShape.up ℕ).next n
  let V := HomologicalComplex.eval AddCommGrpCat.{u} (.up ℕ)
  let S : ShortComplex (J ⥤ AddCommGrpCat.{u}) :=
    ShortComplex.mk (Functor.whiskerLeft F (HomologicalComplex.dNatTrans _ _ p n))
      (Functor.whiskerLeft F (HomologicalComplex.dNatTrans _ _ n q)) (by
        ext j x
        exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom ((F.obj j).d_comp_d p n q)) x)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext j
    have hj := (h j n)
    have hj' : (S.map ((evaluation _ _).obj j)).Exact := hj
    have hz := (ShortComplex.exact_iff_isZero_homology _).mp hj'
    exact (IsZero.of_iso hz (S.mapHomologyIso ((evaluation _ _).obj j)).symm).eq_of_tgt _ _
  have hm := hS.map (colim (J := J) (C := AddCommGrpCat.{u}))
  rw [(colimit F).exactAt_iff' p n q rfl rfl]
  let compare (i : ℕ) := preservesColimitIso (V i) F
  refine ShortComplex.exact_of_iso ?_ hm
  refine ShortComplex.isoMk (compare p).symm (compare n).symm (compare q).symm ?_ ?_
  · apply colimit.hom_ext
    intro j
    change colimit.ι (F ⋙ V p) j ≫ (compare p).inv ≫ (colimit F).d p n =
      colimit.ι (F ⋙ V p) j ≫ colim.map S.f ≫ (compare n).inv
    rw [colimit.ι_map_assoc]
    change colimit.ι (F ⋙ V p) j ≫ (compare p).inv ≫ (colimit F).d p n =
      (F.obj j).d p n ≫ colimit.ι (F ⋙ V n) j ≫ (compare n).inv
    simp only [compare, ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv]
    exact (colimit.ι F j).comm p n
  · apply colimit.hom_ext
    intro j
    change colimit.ι (F ⋙ V n) j ≫ (compare n).inv ≫ (colimit F).d n q =
      colimit.ι (F ⋙ V n) j ≫ colim.map S.g ≫ (compare q).inv
    rw [colimit.ι_map_assoc]
    change colimit.ι (F ⋙ V n) j ≫ (compare n).inv ≫ (colimit F).d n q =
      (F.obj j).d n q ≫ colimit.ι (F ⋙ V q) j ≫ (compare q).inv
    simp only [compare, ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv]
    exact (colimit.ι F j).comm n q

/-- 増大 Čech の完全性は filtered 余極限で保たれる。 -/
theorem ringCechExact_colimit (F : J ⥤ CosimplicialObject.Augmented CommRingCat.{u})
    [HasColimit F] (h : ∀ j, AugmentedRingCechExact (F.obj j)) :
    AugmentedRingCechExact (colimit F) := by
  let := ringCochain_preserves (J := J)
  rw [ringCechExact_iff_acyclic]
  have hc := acyclic_colimit (F ⋙ ringCochain) (fun j => (ringCechExact_iff_acyclic _).mp (h j))
  exact fun n => (hc n).of_iso (preservesColimitIso ringCochain F).symm

/-- 環の射の filtered 余極限は Čech の完全性を保つ。 -/
theorem isCechExact_colimit (F : J ⥤ Arrow CommRingCat.{u})
    (h : ∀ j, IsCechExact (F.obj j)) : IsCechExact (colimit F) := by
  let G : Arrow CommRingCat.{u} ⥤ _ := CosimplicialObject.augmentedCechConerve
  let : G.IsLeftAdjoint := CosimplicialObject.cechConerveAdjunction.isLeftAdjoint
  have hc := ringCechExact_colimit (F ⋙ G) h
  rw [ringCechExact_iff_acyclic] at hc
  change AugmentedRingCechExact (G.obj (colimit F))
  rw [ringCechExact_iff_acyclic]
  exact fun n => (hc n).of_iso (ringCochain.mapIso (preservesColimitIso G F).symm)

end SerrePositivity.Cech
