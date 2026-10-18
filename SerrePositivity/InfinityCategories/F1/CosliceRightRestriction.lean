module

public import SerrePositivity.InfinityCategories.F1.CosliceRestrictionIso

/-!
概要：右 anodyne な図式の包含に沿う coslice 制限の充填性。
方針：任意の部分複体と右 anodyne な包含の pushout-join を内 anodyne として延長する。
規約：標的は quasicategory、図式の包含の向きは coslice の反変方向。
使われ方：Kerodon Proposition 4.3.6.14、Proposition 5.2.5.1 の底の長辺への制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右 anodyne な図式の部分複体への coslice 制限は任意の部分複体包含を持ち上げる。
方針：錐を pushout-join 上で貼り、quasicategory の内ホーン充填で延長する。
規約：試験する包含 A₀ に anodyne 性は不要。
使われ方：Kerodon Proposition 4.3.6.14、三角形の長辺への制限の充填。 -/
lemma sliceUnderRestrict_lift_of_rightAnodyne {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hK : rightAnodyneExtensions K₀.ι) : HasLiftingProperty A₀.ι (sliceUnderRestrict p K₀.ι) := by
  constructor
  intro a b sq
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry b
  have hover : joinMap K₀.ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 (K₀ : SSet.{u})) A₀.ι ≫ H := by
    have hh := congrArg sliceUnderUncurry sq.w
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp] at hh
    exact hh
  let hs := joinUnion_isPushout K₀ A₀
  let T := hs.desc H G hover.symm
  have hT : CommSq T (joinUnion K₀ A₀).ι (terminal.from X)
      (terminal.from (join K A)) := ⟨terminal.hom_ext _ _⟩
  have := joinUnion_innerAnodyne_of_rightAnodyne K₀ A₀ hK (terminal.from X) InnerFibration.mem
  let L := hT.lift
  have hleft : joinMap K₀.ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inl_desc H G hover.symm
  have hright : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inr_desc H G hover.symm
  have hfixed : joinInl K A ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hright
  · apply sliceUnderUncurry_injective (K₀.ι ≫ p)
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
    exact hleft


/-- 概要：右 anodyne な部分図式への coslice 制限は trivial Kan fibration。
方針：全境界の持ち上げ性で判定する。
規約：標的 X の quasicategory 性を仮定する。
使われ方：Kerodon Proposition 4.3.6.14、Proposition 5.2.5.1 の底の制限。 -/
lemma sliceUnderRestrict_trivialKanFibration_of_rightAnodyne {K X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (K₀ : K.Subcomplex)
    (hK : rightAnodyneExtensions K₀.ι) : TrivialKanFibration (sliceUnderRestrict p K₀.ι) :=
  (trivialKanFibration_iff_boundary _).2
    (fun n ↦ sliceUnderRestrict_lift_of_rightAnodyne p (boundary n) K₀ hK)

/-- 概要：部分複体への coslice 制限の充填性を同型表示に移す。
方針：同型に沿う制限との合成の trivial Kan fibration 性を使う。
規約：標的の quasicategory 性は既存の充填性の仮定に含める。
使われ方：Kerodon Proposition 5.2.5.1、底の面を標準単体で表す。 -/
lemma sliceUnderRestrict_trivialKanFibration_subcomplexIso {K L X : SSet.{u}}
    (p : K ⟶ X) (K₀ : K.Subcomplex) (e : L ≅ (K₀ : SSet.{u}))
    [TrivialKanFibration (sliceUnderRestrict p K₀.ι)] :
    TrivialKanFibration (sliceUnderRestrict p (e.hom ≫ K₀.ι)) := by
  rw [← sliceUnderRestrict_comp]
  exact ⟨trivialKanFibrations.comp_mem _ _ TrivialKanFibration.mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：quasicategory 内の三角形から長辺への coslice 制限は trivial Kan fibration。
方針：長辺の右 anodyne 性を部分複体の表示同型を通して適用する。
規約：長辺は δ₁ : Δ[1] → Δ[2]。
使われ方：Kerodon Proposition 5.2.5.1、相対 coslice の消去則の底の仮定。 -/
lemma sliceUnderRestrict_triangleLongEdge {X : SSet.{u}} [Quasicategory X]
    (t : (Δ[2] : SSet.{u}) ⟶ X) :
    TrivialKanFibration (sliceUnderRestrict t (stdSimplex.δ (1 : Fin 3))) := by
  have := sliceUnderRestrict_trivialKanFibration_of_rightAnodyne t
    (stdSimplex.face {(1 : Fin 3)}ᶜ) triangleLongFace_rightAnodyne
  have h := sliceUnderRestrict_trivialKanFibration_subcomplexIso t
    (stdSimplex.face {(1 : Fin 3)}ᶜ) (stdSimplex.faceSingletonComplIso (1 : Fin 3))
  simpa only [stdSimplex.faceSingletonComplIso_hom_ι] using h

end SerrePositivity.InfinityCategories
