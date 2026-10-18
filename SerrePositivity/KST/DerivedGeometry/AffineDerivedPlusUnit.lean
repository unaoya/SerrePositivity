module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedBoundedUnit
public import SerrePositivity.KST.DerivedGeometry.PlusTriangleHomology

/-!
概要：全ての下に有界な加群導来対象でアフィン導来単位は同型。
方針：各固定次数より上の切断を取り、下限保存によって有限区間の比較へ帰着する。
規約：非有界下側への同じ議論の適用は主張しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below 完全忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (ModuleCat.{u} H)]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：下に有界な全対象でアフィン導来随伴の単位は同型。
方針：各次数で上側切断の単位と比較し、残りの高い下限を左右の関手が保存することを使う。
規約：元の全係数層の導来随伴の単位。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below アフィン完全忠実性。
-/
lemma affineDerivedPlus_unit_isIso (K : DerivedCategory.Plus (ModuleCat.{u} H)) :
    IsIso ((affineDerivedPlusAdjunction (R := R) H).unit.app K) := by
  obtain ⟨a, ha⟩ := K.property
  have : K.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).mp ha
  let t := DerivedCategory.Plus.TStructure.t (C := ModuleCat.{u} H)
  let F := affineDerivedTildePlus (R := R) H
  let G := affineDerivedΓPlus (R := R) H
  let adj := affineDerivedPlusAdjunction (R := R) H
  apply (DerivedCategory.Plus.isIso_iff _).mpr
  intro n
  let d := (n - a).toNat
  let b : ℤ := a + d
  have hnb : n ≤ b := by dsimp [b, d]; omega
  let T := (t.triangleLEGT b).obj K
  have hT := t.triangleLEGT_distinguished b K
  have hLge : T.obj₁.IsGE a := by change t.IsGE ((t.truncLE b).obj K) a; infer_instance
  have hLle : T.obj₁.IsLE (a + d) := by
    change t.IsLE ((t.truncLE b).obj K) b
    infer_instance
  have hη : IsIso (adj.unit.app T.obj₁) := affineDerivedPlus_unit_amplitude_isIso H d a T.obj₁
  have hUge : T.obj₃.IsGE (b + 1) := by
    change t.IsGE ((t.truncGT b).obj K) (b + 1)
    infer_instance
  have : T.obj₃.IsGE (n + 1) := t.isGE_of_ge _ _ (b + 1) (by omega)
  have hf : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map T.mor₁) :=
    plusTriangle_homology_mor₁_isIso T hT n
  have hFU : (F.obj T.obj₃).IsGE (b + 1) := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ (b + 1)).mp
    exact exactDerived_isGE (affineCoefficientTildeFunctor (R := R) H) T.obj₃.obj (b + 1)
      ((DerivedCategory.Plus.isGE_ι_obj_iff _ _).mpr hUge)
  have hGFU : ((F ⋙ G).obj T.obj₃).IsGE (b + 1) :=
    rightDerivedPlus_isGE (affineCoefficientΓ (R := R) H) (F.obj T.obj₃) (b + 1)
  have : ((F ⋙ G).mapTriangle.obj T).obj₃.IsGE (n + 1) :=
    t.isGE_of_ge ((F ⋙ G).obj T.obj₃) (n + 1) (b + 1) (by omega)
  have hGf : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map ((F ⋙ G).map T.mor₁)) :=
    plusTriangle_homology_mor₁_isIso ((F ⋙ G).mapTriangle.obj T)
      ((F ⋙ G).map_distinguished T hT) n
  have h := congrArg ((DerivedCategory.Plus.homologyFunctor _ n).map) (adj.unit.naturality T.mor₁)
  simp only [Functor.map_comp, Functor.id_map] at h
  have : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map T.mor₁ ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map (adj.unit.app T.obj₂)) := by
    rw [h]
    infer_instance
  exact (isIso_comp_left_iff ((DerivedCategory.Plus.homologyFunctor _ n).map T.mor₁)
    ((DerivedCategory.Plus.homologyFunctor _ n).map (adj.unit.app T.obj₂))).mp this

end SerrePositivity.KST.DerivedGeometry
