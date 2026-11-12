module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedWeightedHomPostcomposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.BousfieldKanCoherentCocone

/-!
概要：Kan 置換済み Bousfield–Kan coend の反転 Hom 比較の豊穣自然性。
方針：反転重みの end の作用を既存の反変豊穣 Hom 図式の end へ移す。
規約：既存の比較そのものと照合し、coherent 余錐の普遍性とは区別する。
使われ方：HTT 4.2.4.1 の普遍切断点から実際の比較族を復元する代数的入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- coend の反変 Hom 図式を既存の Kan 対象の豊穣 Hom 図式へ移す end 同型。 -/
def kanReflectedBousfieldKanEndIso (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) Y.obj ⋙ SSet.opFunctor) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) :=
  eqToIso (congrArg (fun D ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (D ⋙ SSet.opFunctor))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanBousfieldKanColimitHomDiagram_eq F Y))

/-- 既存の反転 Hom の end に対する Hom(Y,Z).op 全体の後合成。 -/
def kanReflectedBousfieldKanEndPostcomposition
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor) ⊗
        (SimplicialCategory.sHom Y Z).op ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op Z) ⋙ SSet.opFunctor) :=
  ((kanReflectedBousfieldKanEndIso F Y).inv ▷ (SimplicialCategory.sHom Y Z).op) ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedHomPostcomposition (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ)
      (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) Y.obj Z.obj ≫ (kanReflectedBousfieldKanEndIso F Z).hom

/-- Kan 置換後の既存の比較は反転 Hom 空間全体の後合成を保つ。 -/
lemma kanReflectedBousfieldKanColimitHomComparison_enriched_naturality
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (Functor.Monoidal.μIso SSet.opFunctor
        (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y)
        (SimplicialCategory.sHom Y Z)).hom ≫
      SSet.opFunctor.map (MonoidalClosed.comp
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F).obj Y.obj Z.obj) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison F Z =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison F Y ▷ (SimplicialCategory.sHom Y Z).op) ≫
        kanReflectedBousfieldKanEndPostcomposition F Y Z := by
  dsimp only [SimplicialCategory.sHom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_simplicialCategory,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_enrichedCategory]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitUnderlyingHomIso, Iso.trans_hom,
    kanReflectedBousfieldKanEndPostcomposition, kanReflectedBousfieldKanEndIso]
  simp only [comp_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc (eqToIso _).hom]
  rw [Iso.hom_inv_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomComparison_pre_enriched_naturality
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))) Y.obj Z.obj
  have h' := congrArg (fun m ↦ m ≫ (kanReflectedBousfieldKanEndIso F Z).hom) h
  simp only [comp_whiskerRight_assoc, Category.assoc] at h'
  convert h' using 1 <;> rfl

/-- Kan 置換射そのものに対応する既存の反転 Hom の end の普遍切断点。 -/
def kanReflectedBousfieldKanColimitHomPoint (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)) ⋙
        SSet.opFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomPointOfMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ)
    (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))) ≫
      (kanReflectedBousfieldKanEndIso F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)).hom

/-- 置換後の Hom 比較も、その普遍切断点への豊穣後合成から復元できる。 -/
lemma kanReflectedBousfieldKanColimitHomComparison_of_point
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (λ_ (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y).op).inv ≫
        (kanReflectedBousfieldKanColimitHomPoint F ▷
          (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y).op) ≫
          kanReflectedBousfieldKanEndPostcomposition F
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) Y =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison F Y := by
  dsimp only [SimplicialCategory.sHom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_simplicialCategory,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_enrichedCategory]
  dsimp only [kanReflectedBousfieldKanColimitHomPoint,
    kanReflectedBousfieldKanEndPostcomposition,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitUnderlyingHomIso, Iso.trans_hom]
  simp only [comp_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc
    (kanReflectedBousfieldKanEndIso F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)).hom]
  rw [Iso.hom_inv_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomComparison_pre_of_point
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedBousfieldKanColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))) Y.obj
  have h' := congrArg (fun m ↦ m ≫ (kanReflectedBousfieldKanEndIso F Y).hom) h
  simp only [Category.assoc] at h'
  convert h' using 1 <;> rfl

/-- end の普遍切断点は、既存の比較による恒等射の像そのもの。 -/
lemma kanReflectedBousfieldKanColimitHomPoint_eq
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    kanReflectedBousfieldKanColimitHomPoint F =
      (Functor.Monoidal.εIso SSet.opFunctor).hom ≫
        SSet.opFunctor.map (MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F).obj) ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison F
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F) := by
  dsimp only [kanReflectedBousfieldKanColimitHomPoint,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflectedWeightedColimitHomPointOfMap, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitUnderlyingHomIso, Iso.trans_hom]
  rw [← Functor.map_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.internalHom_id_pre]
  rfl

/-- 反転した内部 Hom の単位の零単体は通常の恒等射の反転表示。 -/
lemma reflectedKanIdentity_vertex (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    ((Functor.Monoidal.εIso SSet.opFunctor).hom ≫
      SSet.opFunctor.map (MonoidalClosed.id K.obj)).app (Opposite.op ⦋0⦌) PUnit.unit =
        SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' K K (𝟙 K)) := by
  simp only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
  rfl

/-- 構成済みの coherent な余錐の普遍点は、豊穣復元公式の普遍切断点の像に一致する。 -/
lemma bousfieldKanCoherentConePoint_of_end_point
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConePoint F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F.op
        (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F))).app (Opposite.op ⦋0⦌)
          (ULift.up ((kanReflectedBousfieldKanColimitHomPoint F).app (Opposite.op ⦋0⦌)
            PUnit.unit)) := by
  rw [kanReflectedBousfieldKanColimitHomPoint_eq]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F.op
      (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F))).app (Opposite.op ⦋0⦌)
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison F
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)).app (Opposite.op ⦋0⦌)
          (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' _ _ (𝟙 _))))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F.op
      (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F))).app (Opposite.op ⦋0⦌)
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitHomComparison F
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F)).app (Opposite.op ⦋0⦌)
          (((Functor.Monoidal.εIso SSet.opFunctor).hom ≫
            SSet.opFunctor.map
              (MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F).obj)).app
                (Opposite.op ⦋0⦌) PUnit.unit)))
  rw [reflectedKanIdentity_vertex]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
