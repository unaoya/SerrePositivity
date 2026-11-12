module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：重み付き end と単体順序の反転を、実際の同型として交換する。
方針：内部 Hom の反転比較を multiequalizer の全成分で使い、反転の極限保存を適用する。
規約：重みと係数を同時に反転する。Kan 性やモデル構造は不要。
使われ方：HTT 4.2.4.1、coend の写像空間と反転係数の coherent な錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- end の multiequalizer 図式を反転すると、反転した重みと係数の end 図式に同型。 -/
def oppositeWeightedSectionsDiagramIso (W H : I ⥤ SSet.{u}) :
    (multicospanIndexEnd (Enriched.FunctorCategory.diagram SSet.{u} W H)).multicospan ⋙
        SSet.opFunctor ≅
      (multicospanIndexEnd (Enriched.FunctorCategory.diagram SSet.{u}
        (W ⋙ SSet.opFunctor) (H ⋙ SSet.opFunctor))).multicospan :=
  by
    refine NatIso.ofComponents ?_ ?_
    · intro j
      cases j with
      | left i => exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (W.obj i) (H.obj i)
      | right f => exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (W.obj f.left) (H.obj f.right)
    · rintro (_ | _) (_ | _) (_ | _ | _)
      all_goals
        simp only [Functor.comp_map, MulticospanIndex.multicospan_map_fst,
          MulticospanIndex.multicospan_map_snd, multicospanIndexEnd_fst, multicospanIndexEnd_snd,
          Enriched.FunctorCategory.diagram_obj_map, Enriched.FunctorCategory.diagram_map_app,
          enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
          enrichedOrdinaryCategorySelf_eHomWhiskerRight]
      · simp [MulticospanIndex.multicospan]
      · rename_i f
        change Arrow I at f
        exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_post (W.obj f.left) (H.map f.hom)
      · rename_i f
        change Arrow I at f
        change SSet.opFunctor.map ((pre (W.map f.hom)).app (H.obj f.right)) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (W.obj f.left) (H.obj f.right)).hom =
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (W.obj f.right) (H.obj f.right)).hom ≫
            (pre (SSet.opFunctor.map (W.map f.hom))).app (H.obj f.right).op
        exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_pre (W.map f.hom) (H.obj f.right)
      · simp [MulticospanIndex.multicospan]

/-- 単体順序の反転は重み付き end と厳密な同型で交換する。 -/
def weightedSectionsOppositeIso (W H : I ⥤ SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (W ⋙ SSet.opFunctor) (H ⋙ SSet.opFunctor) :=
  preservesLimitIso SSet.opFunctor
    (multicospanIndexEnd (Enriched.FunctorCategory.diagram SSet.{u} W H)).multicospan ≪≫
      HasLimit.isoOfNatIso (oppositeWeightedSectionsDiagramIso W H)

/-- end の反転同型は各成分で標準の内部 Hom の反転同型。 -/
lemma weightedSectionsOppositeIso_π (W H : I ⥤ SSet.{u}) (i : I) :
    (weightedSectionsOppositeIso W H).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (W ⋙ SSet.opFunctor) (H ⋙ SSet.opFunctor) i =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso (W.obj i) (H.obj i)).hom := by
  change (preservesLimitIso SSet.opFunctor _).hom ≫
      (HasLimit.isoOfNatIso (oppositeWeightedSectionsDiagramIso W H)).hom ≫
        limit.π _ (.left i) = _
  rw [HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  rfl

/-- end の反転同型は係数図式の自然変換と可換。 -/
lemma weightedSectionsOppositeIso_naturality (W : I ⥤ SSet.{u}) {H H' : I ⥤ SSet.{u}}
    (η : H ⟶ H') :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W η) ≫ (weightedSectionsOppositeIso W H').hom =
      (weightedSectionsOppositeIso W H).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (W ⋙ SSet.opFunctor) (Functor.whiskerRight η SSet.opFunctor) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, weightedSectionsOppositeIso_π, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π]
  conv_rhs => rw [← Category.assoc, weightedSectionsOppositeIso_π]
  conv_lhs => rw [← Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π,
    Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_post]
  rfl

/-- 重みの自然同型は前合成により end の同型を誘導する。 -/
def weightedSectionsWeightIso {W W' : I ⥤ SSet.{u}} (e : W ≅ W') (H : I ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W' H ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre e.hom H
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre e.inv H
  hom_inv_id := by rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp, e.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_id]
  inv_hom_id := by rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_comp, e.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_id]

/-- 図式の単体順序を二度反転したものを元の図式へ戻す自然同型。 -/
def diagramDoubleOppositeIso (W : I ⥤ SSet.{u}) :
    (W ⋙ SSet.opFunctor) ⋙ SSet.opFunctor ≅ W :=
  Functor.associator W _ _ ≪≫ Functor.isoWhiskerLeft W SSet.opFunctorCompOpFunctorIso ≪≫
    Functor.rightUnitor W

/-- 反転した重みの end の反転は、元の重み・反転した係数の end に同型。 -/
def weightedSectionsReflectedIso (W H : I ⥤ SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (W ⋙ SSet.opFunctor) H).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (H ⋙ SSet.opFunctor) :=
  weightedSectionsOppositeIso (W ⋙ SSet.opFunctor) H ≪≫
    weightedSectionsWeightIso (diagramDoubleOppositeIso W).symm (H ⋙ SSet.opFunctor)

/-- 重みの前合成と係数の後合成は end 上で可換。 -/
lemma weightedSectionsPre_naturality {W W' : I ⥤ SSet.{u}} (j : W ⟶ W')
    {H H' : I ⥤ SSet.{u}} (η : H ⟶ H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W η =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W' η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre j H' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π]
  conv_lhs => rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_π]
  conv_rhs => rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π]
  rw [Category.assoc, Category.assoc, ← (pre (j.app i)).naturality (η.app i)]

/-- 反転重みの end の同型も係数図式に自然。 -/
lemma weightedSectionsReflectedIso_naturality (W : I ⥤ SSet.{u}) {H H' : I ⥤ SSet.{u}}
    (η : H ⟶ H') :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (W ⋙ SSet.opFunctor) η) ≫
        (weightedSectionsReflectedIso W H').hom =
      (weightedSectionsReflectedIso W H).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap W (Functor.whiskerRight η SSet.opFunctor) := by
  simp only [weightedSectionsReflectedIso, Iso.trans_hom, weightedSectionsWeightIso]
  rw [← Category.assoc, weightedSectionsOppositeIso_naturality, Category.assoc,
    ← weightedSectionsPre_naturality]
  rw [Category.assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
