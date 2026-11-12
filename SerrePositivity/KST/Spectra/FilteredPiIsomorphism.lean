module

public import SerrePositivity.KST.Spectra.FilteredPointing
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：全基点の π_* 同型は Kan 複体の filtered colimit で保たれる。
方針：任意の頂点を一段へ下ろし、その段の under 圏で指定基点の比較を使う。
規約：零次数を含む。空な始段を避けるための仮定を追加しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。filtered Ω 列の Ω 条件。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全基点の π_* 同型となる点つき射は指定基点でも全次数で全単射。
方針：像の基点と指定基点の等式に沿って誘導写像を移す。
規約：零次数を含む全自然数次数。
使われ方：Goerss–Jardine I §7。任意基点の比較を点つき図式へ移す。 -/
theorem pointedHomotopyMap_bijective_of_piIsomorphism {A B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex B.right] (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right)
    (n : ℕ) : Function.Bijective (pointedHomotopyMap n f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n f.right rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)
    rfl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) (hf A.basepoint n)

/-- 概要：Kan 図式の段ごとの全基点 π_* 同型は filtered colimit でも全基点 π_* 同型。
方針：余極限の頂点を一段へ下ろし、後続段に基点を付けてホモトピー類の余極限を比較する。
規約：各段と二つの余極限の Kan 性を明示する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。Ω 条件の filtered colimit 保存。 -/
theorem kanPiIsomorphism_of_filtered {J : Type u} [SmallCategory J] [IsFiltered J]
    {F G : J ⥤ SSet.{u}} [∀ j, KanComplex (F.obj j)] [∀ j, KanComplex (G.obj j)]
    {c : Cocone F} {d : Cocone G} [KanComplex c.pt] [KanComplex d.pt]
    (hc : IsColimit c) (hd : IsColimit d) (t : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j, c.ι.app j ≫ g = t.app j ≫ d.ι.app j)
    (ht : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (t.app j)) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g := by
  intro x n
  obtain ⟨j, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc
    ((SSet.yonedaEquiv (X := c.pt)).symm x)
  change p ≫ c.ι.app j = (SSet.yonedaEquiv (X := c.pt)).symm x at hp
  let xj := SSet.yonedaEquiv p
  have hx : (c.ι.app j).app _ xj = x := by
    apply SSet.yonedaEquiv.symm.injective
    rw [← SSet.yonedaEquiv_symm_comp]
    change (SSet.yonedaEquiv (X := F.obj j)).symm xj ≫ c.ι.app j =
      (SSet.yonedaEquiv (X := c.pt)).symm x
    rw [show (SSet.yonedaEquiv (X := F.obj j)).symm xj = p from
      Equiv.symm_apply_apply _ p]
    exact hp
  subst x
  let c' := pointFromStageCocone F j xj c
  let d' := pointFromStageCocone G j ((t.app j).app _ xj) d
  let g' : c'.pt ⟶ d'.pt := Under.homMk g (by
    change SSet.const ((c.ι.app j).app _ xj) ≫ g =
      SSet.const ((d.ι.app j).app _ ((t.app j).app _ xj))
    rw [SSet.const_comp]
    congr 1
    exact congrArg (fun z : F.obj j ⟶ d.pt ↦ z.app _ xj) (hg j))
  have hcomm (a : Under j) : c'.ι.app a ≫ g' =
      (pointFromStageMap F j xj t).app a ≫ d'.ι.app a := by
    apply Under.UnderMorphism.ext
    exact hg a.right
  have hstage (a : Under j) (m : ℕ) :
      Function.Bijective (pointedHomotopyMap m ((pointFromStageMap F j xj t).app a)) :=
    pointedHomotopyMap_bijective_of_piIsomorphism _ (ht a.right) m
  have hb := pointedHomotopyMap_bijective_of_filtered
    (pointFromStageIsColimit F j xj hc)
    (pointFromStageIsColimit G j ((t.app j).app _ xj) hd)
    (pointFromStageMap F j xj t) g' hcomm hstage n
  have hcx : c'.pt.basepoint = (c.ι.app j).app _ xj := by
    simp only [c', pointFromStageCocone, PointedSimplicialSet.basepoint_ofVertex]
  have hdy : d'.pt.basepoint = g.app _ ((c.ι.app j).app _ xj) := by
    simp only [d', pointFromStageCocone, PointedSimplicialSet.basepoint_ofVertex]
    exact (congrArg (fun z : F.obj j ⟶ d.pt ↦ z.app _ xj) (hg j)).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n g hcx hdy
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint g') rfl hb

/-- 概要：段ごとの全基点 π_* 同型の filtered diagram の選ばれた余極限射も π_* 同型。
方針：余極限射の各脚の可換式と Kan 性を一般の比較へ適用する。
規約：通常の単体集合の filtered colimit。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。telescope の Ω 条件。 -/
theorem colimMap_kanPiIsomorphism {J : Type u} [SmallCategory J] [IsFiltered J]
    {F G : J ⥤ SSet.{u}} [∀ j, KanComplex (F.obj j)] [∀ j, KanComplex (G.obj j)]
    (t : F ⟶ G) (ht : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (t.app j)) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (colimMap t) := by
  let : KanComplex (colimit.cocone F).pt := inferInstanceAs (KanComplex (colimit F))
  let : KanComplex (colimit.cocone G).pt := inferInstanceAs (KanComplex (colimit G))
  exact kanPiIsomorphism_of_filtered (colimit.isColimit F) (colimit.isColimit G) t (colimMap t)
    (colimit.ι_map t) ht

/-- 概要：点つき Kan 図式の段ごとの全基点 π_* 同型は点つき余極限でも保存される。
方針：基点忘却の filtered colimit 保存と全基点の比較を使う。
規約：通常の点つき圏の余極限射について述べる。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。loop を含む図式の Ω 条件。 -/
theorem pointedColimMap_kanPiIsomorphism {J : Type u} [SmallCategory J] [IsFiltered J]
    {D E : J ⥤ PointedSimplicialSet.{u}}
    [∀ j, KanComplex (D.obj j).right] [∀ j, KanComplex (E.obj j).right]
    (t : D ⟶ E) (ht : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (t.app j).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (colimMap t).right := by
  let : ∀ j, KanComplex ((D ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (D.obj j).right)
  let : ∀ j, KanComplex ((E ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (E.obj j).right)
  let c := PointedSimplicialSet.forget.mapCocone (colimit.cocone D)
  let d := PointedSimplicialSet.forget.mapCocone (colimit.cocone E)
  let : KanComplex c.pt := inferInstanceAs (KanComplex (colimit D).right)
  let : KanComplex d.pt := inferInstanceAs (KanComplex (colimit E).right)
  exact kanPiIsomorphism_of_filtered
    (isColimitOfPreserves PointedSimplicialSet.forget (colimit.isColimit D))
    (isColimitOfPreserves PointedSimplicialSet.forget (colimit.isColimit E))
    (Functor.whiskerRight t PointedSimplicialSet.forget) (colimMap t).right
    (fun j ↦ congrArg Under.Hom.right (colimit.ι_map t j)) ht

end

end SerrePositivity.KST.Spectra
