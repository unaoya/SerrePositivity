module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletonFiltrationMono
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CartesianSubfunctorColimit

/-!
概要：単体集合の図式の各単体次数で、有限骨格を Type 値の部分図式として表示する。
方針：骨格の射影の値は元の図式の射そのものであり、単射なら所属を反映することを使う。
規約：図式の全ての射が単射である場合に余極限での単射性へ接続する。
使われ方：Goerss–Jardine VIII §1。骨格の latching 図式の各単体次数。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits SSet
namespace SerrePositivity.KST.Spectra.SkeletonDiagramSubfunctor
end SerrePositivity.KST.Spectra.SkeletonDiagramSubfunctor
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open _root_.SerrePositivity.KST.Spectra.SkeletonDiagramSubfunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type v} [SmallCategory J] (D : J ⥤ SSet.{u}) (n : ℕ)
  (k : SimplexCategoryᵒᵖ)

/-- 有限骨格の各次数での部分図式。 -/
def subfunctor : Subfunctor (D ⋙ (evaluation _ (Type u)).obj k) where
  obj j := ((D.obj j).skeleton n).obj k
  map f := (Subcomplex.image_le_iff _ (D.map f) _).1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.image_le (D.map f) n) k

/-- 部分図式としての表示と実際の骨格の評価は同じ。 -/
def iso : (D ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n) ⋙ (evaluation _ (Type u)).obj k ≅
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.subfunctor D n k).toFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext x; rfl)

/-- 上の同型は実際の骨格の包含を保つ。 -/
lemma iso_inclusion : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.iso D n k).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.subfunctor D n k).ι =
    Functor.whiskerRight (Functor.whiskerLeft D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.inclusion n))
      ((evaluation _ (Type u)).obj k) := by
  apply NatTrans.ext
  funext j
  rfl

/-- 図式の射が単射なら、各次数の部分図式の所属を保存・反映する。 -/
lemma membership_iff (hD : ∀ {i j : J} (f : i ⟶ j), Mono (D.map f))
    {i j : J} (f : i ⟶ j) (x : (D.obj i).obj k) :
    (D.map f).app k x ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.subfunctor D n k).obj j ↔ x ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.subfunctor D n k).obj i := by
  let : Mono (D.map f) := hD f
  change x ∈ (((D.obj j).skeleton n).preimage (D.map f)).obj k ↔
    x ∈ ((D.obj i).skeleton n).obj k
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.preimage_skeleton]

/-- 全ての図式の射が単射なら、各次数での骨格の余極限の包含も単射。 -/
lemma colimit_mono [HasColimitsOfShape J (Type u)]
    (hD : ∀ {i j : J} (f : i ⟶ j), Mono (D.map f)) :
    Mono (colim.map (Functor.whiskerRight
      (Functor.whiskerLeft D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.inclusion n))
      ((evaluation _ (Type u)).obj k))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.iso_inclusion D n k, Functor.map_comp]
  let : Mono (colim.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.subfunctor D n k).ι) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.subfunctor D n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.membership_iff D n k hD)
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
