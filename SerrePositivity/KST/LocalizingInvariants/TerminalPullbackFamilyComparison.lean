module

public import SerrePositivity.KST.LocalizingInvariants.RelativeTerminalPullbackFamilies
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

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
        (functorVertex F) (functorVertex G)
  isInvertible : IsInvertibleEdge edge
  projection : ((ihom P).map ((ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))).app
        (Opposite.op ⦋1⦌) edge.edge =
          (Truncated.Edge.id (X := (truncation 2).obj ((ihom P).obj
            ((ihom (Δ[n] : SSet.{u})).obj ((ihom (horn 2 2 : SSet.{u})).obj X))))
            (functorVertex (F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X)))).edge
  terminal : ((ihom P).map ((pre (simplexLastPoint n)).app (pullbackDiagrams X))).app
        (Opposite.op ⦋1⦌) edge.edge =
          (Truncated.Edge.id (X := (truncation 2).obj ((ihom P).obj
            ((ihom (Δ[0] : SSet.{u})).obj (pullbackDiagrams X))))
            (functorVertex (F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X)))).edge

/-- 元の実辺の類を順方向の射とする、同じ二つの全族の関手同型。 -/
def TerminalPullbackFamilyComparison.iso {P X : SSet.{u}} {n : ℕ}
    {F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)}
    (c : TerminalPullbackFamilyComparison n F G) : FunctorIso F G := by
  have := c.isInvertible
  exact asIso (Truncated.HomotopyCategory.homMk c.edge)

/-- 同じ比較辺を uncurry した全パラメータの実円柱。 -/
def TerminalPullbackFamilyComparison.homotopy {P X : SSet.{u}} {n : ℕ}
    {F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)}
    (c : TerminalPullbackFamilyComparison n F G) : SSet.Homotopy F G :=
  simplicialHomotopyOfFunctorEdge c.edge

lemma familyComparison_post_eq_constant {P E Y : SSet.{u}} {F G : P ⟶ E}
    (p : E ⟶ Y)
    (k : Truncated.Edge (X := (truncation 2).obj ((ihom P).obj E))
      (functorVertex F) (functorVertex G))
    (hk : ((ihom P).map p).app (Opposite.op ⦋1⦌) k.edge =
      (Truncated.Edge.id (X := (truncation 2).obj ((ihom P).obj Y))
        (functorVertex (F ≫ p))).edge) :
    (simplicialHomotopyOfFunctorEdge k).h ≫ p = fst P (Δ[1] : SSet.{u}) ≫ F ≫ p := by
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
    c.homotopy.h ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) =
      fst P (Δ[1] : SSet.{u}) ≫ F ≫
        (pre (simplexLastPoint n)).app (pullbackDiagrams X) :=
  familyComparison_post_eq_constant _ c.edge c.terminal

/-- 同じ二脚を持つ二つの実全族は、その二脚を恒等に保つ可逆な同じ実比較辺で結べる。 -/
lemma exists_terminalPullbackFamilyComparison {P X : SSet.{u}}
    [Quasicategory X] [IsStable X] (n : ℕ)
    (F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (hp : F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
      G ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))
    (ht : F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) =
      G ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X)) :
    Nonempty (TerminalPullbackFamilyComparison n F G) := by
  let sq := terminalPullbackFamilyCorner X n
  let p := (ihom P).map sq.π
  let z := functorVertex (F ≫ sq.π)
  have hFG : F ≫ sq.π = G ≫ sq.π := by
    apply sq.hom_ext
    · rw [Category.assoc, sq.π_fst, Category.assoc, sq.π_fst]
      exact ht
    · rw [Category.assoc, sq.π_snd, Category.assoc, sq.π_snd]
      exact hp
  let v₀ : (vertexFiber p z) _⦋0⦌ := ⟨functorVertex F, by
    rw [pinchedConstant_zero]
    rfl⟩
  let v₁ : (vertexFiber p z) _⦋0⦌ := ⟨functorVertex G, by
    rw [pinchedConstant_zero]
    change functorVertex (G ≫ sq.π) = functorVertex (F ≫ sq.π)
    rw [hFG]⟩
  have hc := vertexFiber_isContractibleKan p z
  have := hc.kanComplex
  let e := terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)
  obtain ⟨k, hk⟩ := homotopyCategory_homMk_surjective v₀ v₁ e.hom
  have hki : IsInvertibleEdge k := by
    change IsIso (Truncated.HomotopyCategory.homMk k)
    rw [hk]
    infer_instance
  let k' := k.map ((truncation 2).map (vertexFiberι p z))
  have hι : vertexFiberι p z ≫ (internalHom.obj (Opposite.op P)).map sq.π = SSet.const z :=
    vertexFiberι_comp p z
  have hpr : vertexFiberι p z ≫
      (ihom P).map ((ihom (Δ[n] : SSet.{u})).map (pullbackProjection X)) =
      SSet.const (functorVertex (F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))) := by
    change vertexFiberι p z ≫ (internalHom.obj (Opposite.op P)).map
      ((internalHom.obj (Opposite.op (Δ[n] : SSet.{u}))).map (pullbackProjection X)) = _
    rw [← sq.π_snd, Functor.map_comp, ← Category.assoc, hι, SSet.const_comp]
    congr 1
    change functorVertex ((F ≫ sq.π) ≫ sq.snd) = _
    rw [Category.assoc, sq.π_snd]
    rfl
  have htr : vertexFiberι p z ≫
      (ihom P).map ((pre (simplexLastPoint n)).app (pullbackDiagrams X)) =
      SSet.const (functorVertex (F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X))) := by
    change vertexFiberι p z ≫ (internalHom.obj (Opposite.op P)).map
      ((internalHom.map (simplexLastPoint n).op).app (pullbackDiagrams X)) = _
    rw [← sq.π_fst, Functor.map_comp, ← Category.assoc, hι, SSet.const_comp]
    congr 1
    change functorVertex ((F ≫ sq.π) ≫ sq.fst) = _
    rw [Category.assoc, sq.π_fst]
    rfl
  refine ⟨⟨k', hki.map _, ?_, ?_⟩⟩
  · change (vertexFiberι p z ≫
      (ihom P).map ((ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))).app
        (Opposite.op ⦋1⦌) k.edge = _
    rw [hpr]
    rfl
  · change (vertexFiberι p z ≫
      (ihom P).map ((pre (simplexLastPoint n)).app (pullbackDiagrams X))).app
        (Opposite.op ⦋1⦌) k.edge = _
    rw [htr]
    rfl

end SerrePositivity.KST.LocalizingInvariants
