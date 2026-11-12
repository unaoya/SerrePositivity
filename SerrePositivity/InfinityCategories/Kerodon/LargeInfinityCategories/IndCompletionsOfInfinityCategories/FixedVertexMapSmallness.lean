module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MapSmallness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorSmallness

/-!
概要：頂点を固定した全写像の小ささを、空間から関手圏と部分圏へ伝える。
方針：coherent な固定対象符号化と全族の uncurry の単射性を使う。
規約：充填性の追加仮定なし。使われ方：図式 comma の実単体の小ささ。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 小さい始域からの、全頂点を固定した写像の型が小さいという性質。 -/
def HasSmallFixedVertexMaps (Y : SSet.{u + 1}) : Prop :=
  ∀ (A : SSet.{u + 1}) (_ : ∀ n, Small.{u} (A.obj n)) (v : A _⦋0⦌ → Y _⦋0⦌),
    Small.{u} {f : A ⟶ Y // ∀ a, f.app (Opposite.op ⦋0⦌) a = v a}

/-- Space∞ への固定頂点の全写像は小さい。 -/
lemma space_hasSmallFixedVertexMaps : HasSmallFixedVertexMaps _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := by
  intro A hA v
  letI := hA
  let code (f : {f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} // ∀ a, f.app (Opposite.op ⦋0⦌) a = v a}) :
      {f : A ⟶ SimplicialNerve _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} //
        ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (f.app (Opposite.op ⦋0⦌) a) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (v a)} :=
    ⟨f.val, fun a => congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (f.property a)⟩
  apply small_of_injective (f := code)
  intro f g h
  have he := congrArg Subtype.val h
  exact Subtype.ext he

/-- 固定頂点の小ささは任意の小さい形状の内部 Hom へ伝わる。 -/
lemma HasSmallFixedVertexMaps.functorSpace {Y : SSet.{u + 1}} (hY : HasSmallFixedVertexMaps Y)
    (L : SSet.{u + 1}) [∀ n, Small.{u} (L.obj n)] :
    HasSmallFixedVertexMaps ((ihom L).obj Y) := by
  intro A hA v
  letI := hA
  have hLA : ∀ n, Small.{u} ((L ⊗ A).obj n) := fun n =>
    inferInstanceAs (Small.{u} (L.obj n × A.obj n))
  let w : (L ⊗ A) _⦋0⦌ → Y _⦋0⦌ := fun z =>
    ((ihom.ev L).app Y).app (Opposite.op ⦋0⦌) (z.1, v z.2)
  haveI := hY (L ⊗ A) hLA w
  let code (f : {f : A ⟶ (ihom L).obj Y // ∀ a, f.app (Opposite.op ⦋0⦌) a = v a}) :
      {f : L ⊗ A ⟶ Y // ∀ z, f.app (Opposite.op ⦋0⦌) z = w z} :=
    ⟨uncurry f.val, by
      intro z
      change ((ihom.ev L).app Y).app _ (z.1, f.val.app _ z.2) = _
      rw [f.property z.2]⟩
  apply small_of_injective (f := code)
  intro f g h
  exact Subtype.ext (uncurry_injective (congrArg Subtype.val h))

/-- 単射の全部分包含を通じて固定頂点の小ささを反映する。 -/
lemma HasSmallFixedVertexMaps.of_mono {X Y : SSet.{u + 1}} (f : X ⟶ Y) [Mono f]
    (hY : HasSmallFixedVertexMaps Y) : HasSmallFixedVertexMaps X := by
  intro A hA v
  let w := fun a => f.app (Opposite.op ⦋0⦌) (v a)
  haveI := hY A hA w
  let code (g : {g : A ⟶ X // ∀ a, g.app (Opposite.op ⦋0⦌) a = v a}) :
      {g : A ⟶ Y // ∀ a, g.app (Opposite.op ⦋0⦌) a = w a} :=
    ⟨g.val ≫ f, fun a => congrArg (f.app (Opposite.op ⦋0⦌)) (g.property a)⟩
  apply small_of_injective (f := code)
  intro g h e
  exact Subtype.ext ((cancel_mono f).mp (congrArg Subtype.val e))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
