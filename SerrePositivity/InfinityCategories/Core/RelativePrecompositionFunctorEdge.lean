module

public import SerrePositivity.InfinityCategories.Core.PrecompositionRelativeLifting

/-!
概要：図式を厳密に固定した二つの延長の間の可逆な関手の辺。
方針：相対内部 Hom の可縮な fiber の二頂点を同型にし、実際の辺で表す。
規約：相対的な射影が恒等辺となることを等式で保持する。
使われ方：Kerodon §4.5.3・4.6.4 の固定した図式上の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単射の普遍的な同値に沿う同じ二つの延長は、固定図式上の可逆な関手の辺で結べる。
方針：相対内部 Hom の trivial Kan fibration の fiber の二頂点の同型を辺で表す。
規約：標的 X は quasicategory、i と j は単射。
使われ方：Kerodon §4.5.3 の相対的な変形の構成。 -/
lemma IsPrecompositionEquivalence.exists_functorEdge_over_pre
    {A B K L X : SSet.{u}} {i : A ⟶ B} [Mono i] (hi : IsPrecompositionEquivalence i)
    (j : K ⟶ L) [Mono j] [Quasicategory X]
    (u v : B ⟶ (ihom L).obj X) (b : B ⟶ (ihom K).obj X)
    (huv : i ≫ v = i ≫ u) (hu : u ≫ (pre j).app X = b) (hv : v ≫ (pre j).app X = b) :
    ∃ k : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj ((ihom L).obj X)))
        (functorVertex u) (functorVertex v), IsInvertibleEdge k ∧
      ((ihom B).map ((pre j).app X)).app (Opposite.op ⦋1⦌) k.edge =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom B).obj ((ihom K).obj X)))
          (functorVertex b)).edge := by
  let p := (pre j).app X
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom i p
  have : TrivialKanFibration sq.π := hi.trivialKanFibration_relative_pre j X sq
  let z := sq.π.app (Opposite.op ⦋0⦌) (functorVertex u)
  have hvz : sq.π.app (Opposite.op ⦋0⦌) (functorVertex v) = z := by
    apply Types.ext_of_isPullback (sq.isPullback.map ((evaluation _ (Type u)).obj (Opposite.op ⦋0⦌)))
    · change (sq.π ≫ sq.fst).app (Opposite.op ⦋0⦌) (functorVertex v) =
        (sq.π ≫ sq.fst).app (Opposite.op ⦋0⦌) (functorVertex u)
      rw [sq.π_fst]
      change functorVertex (i ≫ v) = functorVertex (i ≫ u)
      rw [huv]
    · change (sq.π ≫ sq.snd).app (Opposite.op ⦋0⦌) (functorVertex v) =
        (sq.π ≫ sq.snd).app (Opposite.op ⦋0⦌) (functorVertex u)
      rw [sq.π_snd]
      change functorVertex (v ≫ p) = functorVertex (u ≫ p)
      rw [hv, hu]
  let v₀ : (vertexFiber sq.π z) _⦋0⦌ := ⟨functorVertex u, by rw [pinchedConstant_zero]⟩
  let v₁ : (vertexFiber sq.π z) _⦋0⦌ := ⟨functorVertex v, by rw [pinchedConstant_zero]; exact hvz⟩
  have hc := vertexFiber_isContractibleKan sq.π z
  have := hc.kanComplex
  let h := terminalVertexIso (hc.isTerminalVertex v₀) (hc.isTerminalVertex v₁)
  obtain ⟨k, hk⟩ := homotopyCategory_homMk_surjective v₀ v₁ h.hom
  have hki : IsInvertibleEdge k := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk k)
    rw [hk]
    infer_instance
  let k' := k.map ((truncation 2).map (vertexFiberι sq.π z))
  have hp : vertexFiberι sq.π z ≫ (ihom B).map p = SSet.const (functorVertex b) := by
    change vertexFiberι sq.π z ≫ (internalHom.obj (Opposite.op B)).map p =
      SSet.const (functorVertex b)
    rw [← sq.π_snd, ← Category.assoc, vertexFiberι_comp, SSet.const_comp]
    congr 1
    change ((sq.π ≫ sq.snd).app (Opposite.op ⦋0⦌) (functorVertex u)) = functorVertex b
    rw [sq.π_snd]
    change functorVertex (u ≫ p) = functorVertex b
    rw [hu]
  refine ⟨k', hki.map _, ?_⟩
  change (vertexFiberι sq.π z ≫ (ihom B).map p).app (Opposite.op ⦋1⦌) k.edge = _
  rw [hp]
  rfl

end SerrePositivity.InfinityCategories
