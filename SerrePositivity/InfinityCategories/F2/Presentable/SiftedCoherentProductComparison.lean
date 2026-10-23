module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentProductTotalEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedProductComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalObject

/-!
概要：coherent な点ごとの積の元の余極限 Kan 模型から、二つの元の余極限模型の積へ比較する。
方針：小さい全空間の指定比較の Kan 置換に、元の二射影の積比較を続ける。
規約：両脚と単位は元の射を保持。使われ方：sifted 余極限の有限積保存の native な錐への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] kanTensor_isKan
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の coherent 余極限 Kan 模型における、指定二射影の積比較。 -/
def coherentProductTotalKanComparison :
    F2.coherentDiagramTotalKan (coherentSpaceTensorProduct F G) ⟶
      F2.coherentDiagramTotalKan F ⊗ F2.coherentDiagramTotalKan G :=
  F2.continuousKanReplacement.map (coherentSpaceTensorProductTotalComparison F G) ≫
    F2.totalKanProductComparison (smallLeftUnstraighteningProjection F)
      (smallLeftUnstraighteningProjection G)

/-- 元の比較の第一脚は、指定第一射影の全空間作用の Kan 置換そのもの。 -/
lemma coherentProductTotalKanComparison_fst :
    coherentProductTotalKanComparison F G ≫
      fst (F2.coherentDiagramTotalKan F) (F2.coherentDiagramTotalKan G) =
        F2.continuousKanReplacement.map (coherentSpaceTensorProductTotalFst F G) := by
  dsimp only [F2.coherentDiagramTotalKan]
  rw [coherentProductTotalKanComparison, F2.totalKanProductComparison,
    Category.assoc, lift_fst, ← Functor.map_comp,
    coherentSpaceTensorProductTotalComparison_fst]

/-- 元の比較の第二脚も、指定第二射影の全空間作用の Kan 置換そのもの。 -/
lemma coherentProductTotalKanComparison_snd :
    coherentProductTotalKanComparison F G ≫
      snd (F2.coherentDiagramTotalKan F) (F2.coherentDiagramTotalKan G) =
        F2.continuousKanReplacement.map (coherentSpaceTensorProductTotalSnd F G) := by
  dsimp only [F2.coherentDiagramTotalKan]
  rw [coherentProductTotalKanComparison, F2.totalKanProductComparison,
    Category.assoc, lift_snd, ← Functor.map_comp,
    coherentSpaceTensorProductTotalComparison_snd]

/-- 比較は、元の二つの全空間作用と元の Kan 置換の単位に厳密に整合する。 -/
lemma coherentProductTotalKanComparison_unit :
    F2.continuousKanReplacementUnit.app
      (smallLeftUnstraightening (coherentSpaceTensorProduct F G)) ≫
      coherentProductTotalKanComparison F G =
        lift (coherentSpaceTensorProductTotalFst F G ≫
          F2.continuousKanReplacementUnit.app (smallLeftUnstraightening F))
          (coherentSpaceTensorProductTotalSnd F G ≫
            F2.continuousKanReplacementUnit.app (smallLeftUnstraightening G)) := by
  apply CartesianMonoidalCategory.hom_ext
  · erw [Category.assoc, coherentProductTotalKanComparison_fst, lift_fst]
    exact (F2.continuousKanReplacementUnit.naturality _).symm
  · erw [Category.assoc, coherentProductTotalKanComparison_snd, lift_snd]
    exact (F2.continuousKanReplacementUnit.naturality _).symm

/-- sifted な任意の底上で、元の coherent 積図式の余極限 Kan 比較は弱ホモトピー同値。 -/
lemma coherentProductTotalKanComparison_isWeakHomotopyEquivalence [IsSiftedInfinity B] :
    IsWeakHomotopyEquivalence (coherentProductTotalKanComparison F G) :=
  (F2.continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (coherentSpaceTensorProductTotalComparison_isWeakHomotopyEquivalence F G)).comp
    (totalKanProductComparison_isWeakHomotopyEquivalence_of_sifted _ _)

/-- 同じ元の余極限 Kan 比較は、実際の単体的ホモトピー逆を持つ。 -/
lemma coherentProductTotalKanComparison_homotopyEquivalence [IsSiftedInfinity B] :
    IsSimplicialHomotopyEquivalence (coherentProductTotalKanComparison F G) :=
  (coherentProductTotalKanComparison_isWeakHomotopyEquivalence F G).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
