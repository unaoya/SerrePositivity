module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTriangleZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport

/-!
概要：元の実零化二単体の全 Hom 頂点を終関手の零成分へ置く。
方針：各元 path から元の最大 path への辺を全 Hom 作用で写す。
規約：元二単体とその全高次 Hom 作用を保持。使われ方：指定全境界の相対充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "X₀" => dgOdotMilnorNuNullTriangleStableObject R d 0
local notation "X₂" => dgOdotMilnorNuNullTriangleStableObject R d 2
local notation "σ" => dgOdotMilnorNuNullTriangle R d 0
/-- 概要：元の零化三角形の両端を結ぶ実 path 圏。
方針：元二単体の豊穣 Hom の始域を固定する。
規約：中間頂点を含む全 path。使われ方：全 Hom 作用の零性。 -/
abbrev DGOdotMilnorNuNullTrianglePath := SimplicialThickening.Path
  (ULift.up.{u + 1} (0 : Fin 3)) (ULift.up.{u + 1} (2 : Fin 3))

/-- 概要：元の上三角形の端点間の実全 Hom 作用。
方針：同じ元の二単体の豊穣 Hom 写像を読む。
規約：端点輸送前の元 Hom。使われ方：元最大 path の合成との照合。 -/
def dgOdotMilnorNuNullUpperHom : nerve DGOdotMilnorNuNullTrianglePath.{u} ⟶
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (X₀) (X₂) :=
  (dgOdotMilnorNuNullTriangle R d 0).map ⟨ULift.up (0 : Fin 3)⟩ ⟨ULift.up (2 : Fin 3)⟩
local notation "M" => dgOdotMilnorNuNullUpperHom R d

/-- 概要：元両端の実完全関手圏。
方針：同じ豊穣 Hom の core 包含先を固定する。
規約：元始域と元終域。使われ方：全零成分の終頂点判定。 -/
abbrev DGOdotMilnorNuNullUpperExactFunctors : SSet.{u + 1} := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (X₀) (X₂)
local notation "E" => DGOdotMilnorNuNullUpperExactFunctors R d

/-- 概要：元の完全関手圏の core 包含。
方針：同じ豊穣 Hom の基礎完全関手を保持する。
規約：元の全単体。使われ方：全零成分の因子分解。 -/
def dgOdotMilnorNuNullUpperHomInclusion :
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (X₀) (X₂) ⟶ (E) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (X₀) (X₂) : SSet.{u + 1})).ι
local notation "ι" => dgOdotMilnorNuNullUpperHomInclusion R d

/-- 概要：元の上三角形の両端を結ぶ最大 path。
方針：元区間全体を台に持つ path を使う。
規約：同じ二端点。使われ方：任意 path と零合成の比較。 -/
def dgOdotMilnorNuNullUpperMaximalPath : DGOdotMilnorNuNullTrianglePath.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMaximalPath
    (show (ULift.up (0 : Fin 3) : ULift.{u + 1} (Fin 3)) ≤ ULift.up 2 by decide)
local notation "Pmax" => dgOdotMilnorNuNullUpperMaximalPath

local instance nuNullUpperSource_quasicategory : Quasicategory (X₀).obj :=
  (X₀).isQuasicategory
local instance nuNullUpperTarget_quasicategory : Quasicategory (X₂).obj :=
  (X₂).isQuasicategory
local instance nuNullUpperExact_quasicategory : Quasicategory (E) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors_quasicategory (X₀) (X₂)

/-- 概要：元の最大 path の実合成は完全関手圏の終頂点。
方針：同じ実零角経由の全零性を点ごとの終対象性へ移す。
規約：元の合成完全射を保持。使われ方：元 Hom 全像の終成分判定。 -/
lemma dgOdotMilnorNuNullTriangleMaximal_isTerminal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (X₀) (X₂)
      (dgOdotMilnorNuNullTriangleMaximalComposite R d)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgOdotMilnorNuNullTriangleMaximalComposite R d).hom)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
    (fun x => (dgOdotMilnorNuNullTriangleMaximalComposite_zero R d x).2)

/-- 概要：元最大 path の Hom 頂点は同じ実合成完全射の頂点。
方針：元豊穣関手の通常射と全 Hom の単位評価の照合を使う。
規約：指定した元頂点の等号。使われ方：終対象性の輸送。 -/
lemma dgOdotMilnorNuNullTriangleMaximal_vertex :
    ((M) ≫ (ι)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Pmax)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (X₀) (X₂) (dgOdotMilnorNuNullTriangleMaximalComposite R d) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex (σ) (Pmax)
  exact congrArg (fun x => (ι).app (Opposite.op ⦋0⦌) x) h.symm

/-- 概要：元二単体の任意 path の Hom 頂点は同じ完全関手圏の終頂点。
方針：最大 path への元包含辺を Kan Hom へ写し、同じ可逆辺で終対象性を戻す。
規約：元の全 path を保持。使われ方：全 Hom の零成分への因子分解。 -/
lemma dgOdotMilnorNuNullTriangle_path_isTerminal (P : DGOdotMilnorNuNullTrianglePath.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (((M) ≫ (ι)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex P)) := by
  let f : P ⟶ (Pmax) := ⟨homOfLE (show P.I ⊆ (Pmax).I from
    fun x hx => ⟨P.left_le x hx, P.le_right x hx⟩)⟩
  let e : (nerve DGOdotMilnorNuNullTrianglePath.{u}).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex P) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Pmax)) :=
    SSet.Edge.mk (ComposableArrows.mk₁ f) (ComposableArrows.ext₀ rfl)
      (ComposableArrows.ext₀ rfl)
  let e' := e.map (M)
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e'.toTruncated :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (SimplicialCategory.sHom
      (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (X₀) (X₂))) _
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk (e'.map (ι)).toTruncated) :=
    hi.map (ι)
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (((M) ≫ (ι)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Pmax))) :=
    (dgOdotMilnorNuNullTriangleMaximal_vertex R d).symm ▸
      dgOdotMilnorNuNullTriangleMaximal_isTerminal R d
  exact ht.of_vertexIso (asIso
    (SSet.Truncated.HomotopyCategory.homMk (e'.map (ι)).toTruncated)).symm

/-- 概要：元上三角形の Hom の全零単体は完全関手圏の終頂点。
方針：零次射列をその唯一の対象で回収し、元 path の終対象性を使う。
規約：任意の元零単体。使われ方：全単体の零成分への制限。 -/
lemma dgOdotMilnorNuNullUpperHom_vertex_isTerminal
    (a : (nerve DGOdotMilnorNuNullTrianglePath.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (((M) ≫ (ι)).app (Opposite.op ⦋0⦌) a) := by
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (a.obj 0) = a := ComposableArrows.ext₀ rfl
  exact ha ▸ dgOdotMilnorNuNullTriangle_path_isTerminal R d (a.obj 0)

/-- 概要：同じ上三角形の元 Hom 全像を終関手の零成分へ因子分解する。
方針：全頂点の終対象性で元写像を同じ全部分複体へ制限する。
規約：全高次単体を保持。使われ方：元実面の相対高次充填。 -/
def dgOdotMilnorNuNullUpperHomTerminalFactor :
    nerve DGOdotMilnorNuNullTrianglePath.{u} ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (E) : SSet.{u + 1}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((M) ≫ (ι))
    (dgOdotMilnorNuNullUpperHom_vertex_isTerminal R d)

/-- 概要：零成分への全因子分解は同じ元 Hom 作用を厳密に回収する。
方針：全部分複体への持ち上げの包含式を使う。
規約：全単体の等号。使われ方：指定二単体そのものの保持。 -/
lemma dgOdotMilnorNuNullUpperHomTerminalFactor_inclusion :
    dgOdotMilnorNuNullUpperHomTerminalFactor R d ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (E)).ι =
      (M) ≫ (ι) := rfl

end SerrePositivity.KST.SConstruction
