module
public import SerrePositivity.KST.SConstruction.DiagonalObjects
public import SerrePositivity.KST.SConstruction.CoreSimplicial
public import SerrePositivity.KST.SConstruction.StableModels

/-! # 全 gapped 図式の object 単体集合
概要：各 S_n の零単体から s•C を作り、core の対角実現への比較射を定義する。
方針：零次数の評価と core の全頂点性を使う。
規約：全 gapped 図式を保つ。使われ方：McCarthy 法の object 加法性と object/core 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：各次数の全 gapped 図式を単体とする object S 構成。
方針：S•C の各行の零単体を取る。
規約：core や第一行の選択模型で置換しない。使われ方：McCarthy 型の単体ホモトピー。 -/
def objectSConstruction (C : SSet.{u}) : SSet.{u} := diagonalObjects (simplicialSConstruction C)

/-- 概要：object S 構成の n 単体は全 gapped S_n の零単体そのもの。
方針：零次数での評価の定義を使う。
規約：型の厳密な等号。使われ方：原典の object 単体集合との照合。 -/
lemma objectSConstruction_obj (C : SSet.{u}) (n : ℕ) :
    (objectSConstruction C).obj (Opposite.op ⦋n⦌) =
      (sConstruction n C).obj (Opposite.op ⦋0⦌) := rfl

/-- 概要：core と元の単体集合の頂点の同定を自然同型として束ねる。
方針：全頂点性と部分型の射影を互いに逆にする。
規約：quasicategory 性は不要。使われ方：object から core の object への比較。 -/
def coreVertexNatIso :
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌) :=
  NatIso.ofComponents (fun X => Equiv.toIso {
    toFun := fun x => ⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex x⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => Subtype.ext rfl }) (by
      intro X Y f
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      rfl)

/-- 概要：二重単体集合の object と各行の core の object は自然に同型。
方針：core の全頂点性の同型を各行に前合成する。
規約：二重単体集合の全ての射について自然。使われ方：object/core 対角比較の自然性。 -/
def coreDiagramObjectsIso :
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) ≅
      (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) :=
  NatIso.ofComponents (fun X => Functor.isoWhiskerLeft X coreVertexNatIso) (by
    intro X Y f
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl)

/-- 概要：各行の object から各行の core の対角への自然な比較。
方針：core の全頂点性と内部の定数退化の自然変換を合成する。
規約：弱同値性は含めない。使われ方：加法性の object/core 比較の自然性。 -/
def objectCoreDiagonalComparisonNat :
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) ⟶
      (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⋙ simplicialDiagonalFunctor :=
  coreDiagramObjectsIso.hom ≫ Functor.whiskerLeft
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} SSet.{u}).obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor)
    diagonalObjectInclusionNat

/-- 概要：object S 構成と core S• の零単体の単体集合は同型。
方針：core の全頂点性の自然同型を S•C に前合成する。
規約：S の単体作用素について厳密に自然。使われ方：object/core 実現比較の源の同定。 -/
def objectSCoreVertexIso (C : SSet.{u}) :
    objectSConstruction C ≅ diagonalObjects (simplicialCoreSConstruction C) :=
  Functor.isoWhiskerLeft (simplicialSConstruction C) coreVertexNatIso

/-- 概要：object S 構成から core の対角実現への実際の比較射。
方針：core の零単体への同型に内部の定数退化を合成する。
規約：弱同値性は別に証明する。使われ方：Fiore–Pieper Proposition 4.27 の比較対象。 -/
def objectToCoreSRealization (C : SSet.{u}) :
    objectSConstruction C ⟶ simplicialDiagonalFunctor.obj (simplicialCoreSConstruction C) :=
  (objectSCoreVertexIso C).hom ≫ diagonalObjectInclusion (simplicialCoreSConstruction C)

/-- 概要：object S から core 実現への射は一般の object/core 自然変換の成分。
方針：二つの定義を照合する。
規約：厳密等号。使われ方：具体的な比較の自然性。 -/
lemma objectToCoreSRealization_eq (C : SSet.{u}) :
    objectToCoreSRealization C =
      objectCoreDiagonalComparisonNat.app (simplicialSConstruction C) := rfl

/-- 概要：object S と core 実現の比較は S 図式の射について自然。
方針：一般の object/core 自然変換の自然性を適用する。
規約：全 gapped S 図式の自然変換を入力とする。使われ方：加法性の比較図式。 -/
lemma objectToCoreSRealization_naturality {C D : SSet.{u}}
    (f : simplicialSConstruction C ⟶ simplicialSConstruction D) :
    Functor.whiskerRight f
        ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)) ≫
      objectToCoreSRealization D =
        objectToCoreSRealization C ≫
          simplicialDiagonalFunctor.map (Functor.whiskerRight f _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) :=
  objectCoreDiagonalComparisonNat.naturality f

/-- 概要：object S 構成を安定な入力について関手化する。
方針：S の自己関手の図式を反転し、底の零単体で評価する。
規約：cofiber 保存射に関する関手。使われ方：加法性の subobject・quotient の射。 -/
def objectSConstructionFunctor : StableModel.{u} ⥤ SSet.{u} :=
  simplicialStableEndofunctor.flip ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ StableModel.{u} (Type u)).obj
      (stableModelForget ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))

/-- 概要：安定な入力の object 関手は底の全 gapped object S 構成そのもの。
方針：自己関手での評価と底の S•C の定義を照合する。
規約：単体集合の厳密等号。使われ方：加法性の型の照合。 -/
lemma objectSConstructionFunctor_obj (X : StableModel.{u}) :
    objectSConstructionFunctor.obj X = objectSConstruction X.carrier := rfl

end SerrePositivity.KST.SConstruction
