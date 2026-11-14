module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.ConcreteCubicalCategory
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Cubes.CubeJoinDetection

/-! # 具体的な cubical 射の有限 signature
概要：元の射を零頂点と一座標頂点での値へ送り、その有限データが射の等号を検出する。
方針：元の生成射の join 保存と support による回収式を使う。
規約：零次元と一端点の定数射を含む。使われ方：生成射の語の具体的な意味の判定。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の射の零頂点と全ての一座標頂点での値。 -/
def concreteCubeSignature {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex Y.dimension × (Fin X.dimension → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex Y.dimension) :=
  (f.val ⊥, fun i => f.val (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom X.dimension i))

/-- 元の具体的な射は、その有限 signature から全頂点で回収される。 -/
lemma concreteCubeMap_eval {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension) :
    f.val x = (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature f).1 ⊔
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexSupport x).sup (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature f).2 :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinMap_eval (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_sup f.property) x

/-- 具体的な射の signature は単射で、語の表示を持ち込まずに射の等号を検出する。 -/
lemma concreteCubeSignature_injective (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature (X := X) (Y := Y)) := by
  intro f g h
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_ext f.property g.property (congrArg Prod.fst h)
    (fun i => congrFun (congrArg Prod.snd h) i)

/-- 元の射の等号は、有限 signature の等号と同値。 -/
lemma concreteCubeSignature_eq_iff {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f g : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature f = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature g ↔ f = g :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature_injective X Y).eq_iff

/-- 元の合成の signature は、前段の同じ有限個の値への後段の作用。 -/
lemma concreteCubeSignature_comp {X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature (f ≫ g) =
      (g.val (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature f).1, fun i => g.val ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature f).2 i)) :=
  rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeMap_eval := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeMap_eval

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeSignature := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeSignature_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeSignature_eq_iff := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature_eq_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeSignature_injective := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeSignature_injective
