module

public import SerrePositivity.KST.LocalizingInvariants.RelativeTerminalPullbackFamilies
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：同じ cospan と終端列を持つ実 pullback 族を、両射影上で恒等な同じ辺で比較する。
方針：二脚を記憶する元の corner の内部 Hom の可縮ファイバーで比較辺を構成する。
規約：cospan または終端列を忘れた比較に置き換えず、指定した二つの全族を保持する。
使われ方：回収済み余錐円柱の実前段と、元の分母精密化の全正方形族との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 指定した二つの実全族を、両射影上で恒等な同じ実辺で結ぶ比較データ。 -/
structure TerminalPullbackFamilyComparison {P X : SSet.{u}} (n : ℕ)
    (F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)) where
  edge : Truncated.Edge
        (X := (truncation 2).obj ((ihom P).obj
          ((ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
  isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge edge
  projection : ((ihom P).map ((ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))).app
        (Opposite.op ⦋1⦌) edge.edge =
          (Truncated.Edge.id (X := (truncation 2).obj ((ihom P).obj
            ((ihom (Δ[n] : SSet.{u})).obj ((ihom (horn 2 2 : SSet.{u})).obj X))))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X)))).edge
  terminal : ((ihom P).map ((pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X))).app
        (Opposite.op ⦋1⦌) edge.edge =
          (Truncated.Edge.id (X := (truncation 2).obj ((ihom P).obj
            ((ihom (Δ[0] : SSet.{u})).obj (pullbackDiagrams X))))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)))).edge

/-- 元の実辺の類を順方向の射とする、同じ二つの全族の関手同型。 -/
def TerminalPullbackFamilyComparison.iso {P X : SSet.{u}} {n : ℕ}
    {F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)}
    (c : TerminalPullbackFamilyComparison n F G) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := by
  have := c.isInvertible
  exact asIso (Truncated.HomotopyCategory.homMk c.edge)

/-- 同じ比較辺を uncurry した全パラメータの実円柱。 -/
def TerminalPullbackFamilyComparison.homotopy {P X : SSet.{u}} {n : ℕ}
    {F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)}
    (c : TerminalPullbackFamilyComparison n F G) : SSet.Homotopy F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge c.edge

lemma familyComparison_post_eq_constant {P E Y : SSet.{u}} {F G : P ⟶ E}
    (p : E ⟶ Y)
    (k : Truncated.Edge (X := (truncation 2).obj ((ihom P).obj E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (hk : ((ihom P).map p).app (Opposite.op ⦋1⦌) k.edge =
      (Truncated.Edge.id (X := (truncation 2).obj ((ihom P).obj Y))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ p))).edge) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k).h ≫ p = fst P (Δ[1] : SSet.{u}) ≫ F ≫ p := by
  change uncurry (SSet.yonedaEquiv.symm k.edge) ≫ p = _
  rw [← uncurry_natural_right, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm
    (((ihom P).map p).app (Opposite.op ⦋1⦌) k.edge)) = _
  rw [hk]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  rfl

/-- 元の cospan 全族は比較円柱の全時刻で固定される。 -/
lemma TerminalPullbackFamilyComparison.homotopy_projection {P X : SSet.{u}} {n : ℕ}
    {F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)}
    (c : TerminalPullbackFamilyComparison n F G) :
    c.homotopy.h ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
      fst P (Δ[1] : SSet.{u}) ≫ F ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) :=
  familyComparison_post_eq_constant _ c.edge c.projection

/-- 元の終端全列も、同じ比較円柱の全時刻で固定される。 -/
lemma TerminalPullbackFamilyComparison.homotopy_terminal {P X : SSet.{u}} {n : ℕ}
    {F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)}
    (c : TerminalPullbackFamilyComparison n F G) :
    c.homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) =
      fst P (Δ[1] : SSet.{u}) ≫ F ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) :=
  familyComparison_post_eq_constant _ c.edge c.terminal

/-- 同じ二脚を持つ二つの実全族は、その二脚を恒等に保つ可逆な同じ実比較辺で結べる。 -/
lemma exists_terminalPullbackFamilyComparison {P X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (n : ℕ)
    (F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (hp : F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
      G ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))
    (ht : F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) =
      G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)) :
    Nonempty (TerminalPullbackFamilyComparison n F G) := by
  let sq := terminalPullbackFamilyCorner X n
  let p := (ihom P).map sq.π
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ sq.π)
  have hFG : F ≫ sq.π = G ≫ sq.π := by
    apply sq.hom_ext
    · rw [Category.assoc, sq.π_fst, Category.assoc, sq.π_fst]
      exact ht
    · rw [Category.assoc, sq.π_snd, Category.assoc, sq.π_snd]
      exact hp
  let v₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p z) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    rfl⟩
  let v₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p z) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ sq.π) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ sq.π)
    rw [hFG]⟩
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p z
  have := hc.kanComplex
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective v₀ v₁ e.hom
  have hki : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge k := by
    change IsIso (Truncated.HomotopyCategory.homMk k)
    rw [hk]
    infer_instance
  let k' := k.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p z))
  have hι : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p z ≫ (internalHom.obj (Opposite.op P)).map sq.π = SSet.const z :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp p z
  have hpr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p z ≫
      (ihom P).map ((ihom (Δ[n] : SSet.{u})).map (pullbackProjection X)) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p z ≫ (internalHom.obj (Opposite.op P)).map
      ((internalHom.obj (Opposite.op (Δ[n] : SSet.{u}))).map (pullbackProjection X)) = _
    rw [← sq.π_snd, Functor.map_comp, ← Category.assoc, hι, SSet.const_comp]
    congr 1
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((F ≫ sq.π) ≫ sq.snd) = _
    rw [Category.assoc, sq.π_snd]
    rfl
  have htr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p z ≫
      (ihom P).map ((pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X))) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p z ≫ (internalHom.obj (Opposite.op P)).map
      ((internalHom.map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n).op).app (pullbackDiagrams X)) = _
    rw [← sq.π_fst, Functor.map_comp, ← Category.assoc, hι, SSet.const_comp]
    congr 1
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((F ≫ sq.π) ≫ sq.fst) = _
    rw [Category.assoc, sq.π_fst]
    rfl
  refine ⟨⟨k', hki.map _, ?_, ?_⟩⟩
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p z ≫
      (ihom P).map ((ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))).app
        (Opposite.op ⦋1⦌) k.edge = _
    rw [hpr]
    rfl
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p z ≫
      (ihom P).map ((pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X))).app
        (Opposite.op ⦋1⦌) k.edge = _
    rw [htr]
    rfl

end SerrePositivity.KST.LocalizingInvariants
