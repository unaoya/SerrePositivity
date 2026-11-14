module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentRightConeFixedFront

/-!
# 通常の全単体を表す coherent 右錐

概要：全ての最後 Hom が通常射に定値な右錐を元の通常図式へ戻す。
方針：元の全対象と全 Hom を端点の等号で正規化する。
規約：全ての path の値を比較し、辺の類だけでは代用しない。
使われ方：native roof prism の零端。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}

lemma orderHom_const (G : Fin (n + 2) ⥤ C) (i j : Fin (n + 2)) (hij : i ≤ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.orderDiagramEnrichedHom
      ((⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin (n + 2)) →o
        Fin (n + 2)).toFunctor ⋙ G) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex j) =
    toUnit _ ≫ eHomEquiv SSet (G.map (homOfLE hij)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (G.map (homOfLE hij))) d =
    (eHomEquiv SSet (G.map (homOfLE hij))).app _ PUnit.unit
  simpa only [SimplicialCategory.homEquiv', Equiv.trans_apply] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eHomEquiv SSet (G.map (homOfLE hij))) d).symm

variable (F : Fin (n + 1) ⥤ C) (Y : C)
  (L : ∀ i : Fin (n + 1),
    SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (n + 1))) ⟶
      SimplicialCategory.sHom (F.obj i) Y)
  (hL : ∀ (i j : Fin (n + 1)) (hij : i ≤ j),
    eComp SSet (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex j.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (n + 1))) ≫ L i =
      lift (toUnit _ ≫ eHomEquiv SSet (F.map (homOfLE hij))) (snd _ _ ≫ L j) ≫
        eComp SSet (F.obj i) (F.obj j) Y)

lemma diagram_eq_order (G : Fin (n + 2) ⥤ C)
    (hc : ∀ i : Fin (n + 1), F.obj i = G.obj i.castSucc)
    (hy : Y = G.obj (Fin.last (n + 1)))
    (hf : ∀ (i j : Fin (n + 1)) (hij : i ≤ j),
      HEq (F.map (homOfLE hij))
        (G.map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij))))
    (hl : ∀ i, L i ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (hc i) hy) =
      toUnit _ ≫ eHomEquiv SSet (G.map (homOfLE (Fin.le_last i.castSucc)))) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeFunctor.diagram F Y L hL = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋n + 1⦌) G := by
  have ho (i : Fin (n + 2)) : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y i = G.obj i := by
    induction i using Fin.lastCases
    · exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last F Y).trans hy
    · rename_i i
      exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast F Y i).trans (hc i)
  apply EnrichedFunctor.ext SSet (fun i => ho i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (ho i) (ho j)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.orderDiagramEnrichedHom
      ((⟨ULift.down, fun _ _ h => h⟩ : ULift.{u} (Fin (n + 2)) →o
        Fin (n + 2)).toFunctor ⋙ G) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex j)
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    rw [orderHom_const G _ _ (le_refl _)]
    have hu : eId SSet Y ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hy hy) =
        eId SSet (G.obj (Fin.last (n + 1))) := by
      cases hy
      simp only [eqToHom_refl, Category.comp_id]
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last F Y) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last F Y))) ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom hy hy) := by
        simp only [Category.assoc, eqToHom_trans]
      _ = _ := by
        rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom_last_last, Category.assoc, hu]
        congr 2
        rw [← eHomEquiv_id]
        congr 1
        exact (G.map_id _).symm
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    omega
  case cast.last i =>
    rw [orderHom_const G _ _ (Fin.le_last _)]
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L i.castSucc (Fin.last (n + 1)) ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast F Y i) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last F Y))) ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom (hc i) hy) := by
        simp only [Category.assoc, eqToHom_trans]
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom_cast_last, hl]
  case cast.cast i j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hij := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.front_le i j (P.obj 0)
    have h : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L i.castSucc j.castSucc ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (ho i.castSucc) (ho j.castSucc)) =
        toUnit _ ≫ eHomEquiv SSet
          (G.map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij))) := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_cast_cast_normalized F Y L i j (hc i) (hc j), _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.frontHom_const F i j hij,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitHom_transport (hc i) (hc j) _ _ (hf i j hij)]
    rw [orderHom_const G _ _ (Fin.castSucc_le_castSucc_iff.mpr hij)]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h d) P

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
