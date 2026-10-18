module

public import SerrePositivity.KST.Descent.ReductionDescent

/-!
# 同変な単射による点のファイバーの推移性の移行

## 概要
同変な可換正方形の始域側が点上単射なら、点のファイバーの推移性を移す。

## 方針
元のファイバーを結ぶ群元を選び、同変性と点の単射性で戻す。

## 規約
幾何的推移性の定義との同一視はせず、基礎点の推移性だけを比較する。

## 使われ方
論文 補題 3.3・定理 3.1 の交わりと、始域・基底を同時に被約化する還元。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：始域側が点上単射な同変正方形で推移性を移す（論文 定理 3.1）。
方針：可換式で元のファイバーへ移し、選んだ群元を単射性で戻す。
規約：基底側の射の単射性・全射性は不要。
使われ方：閉和の交わりの指定射と、両側の被約化の点の推移性。 -/
theorem fiberTransitivity_of_injective_square {S : Scheme.{u}}
    {X Y X' Y' : FiniteTypeSchemes S} {G : Type*} [Group G]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (square : a ≫ f = f' ≫ b) (action : G →* Aut X) (action' : G →* Aut X')
    (equivariant : ∀ g, (action' g).asIso.hom ≫ a = a ≫ (action g).asIso.hom)
    (injective : Function.Injective a.hom.left)
    (transitive : ∀ x y : X.obj.left, f.hom.left x = f.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (x y : X'.obj.left) (same_base : f'.hom.left x = f'.hom.left y) :
    ∃ g : G, (action' g).asIso.hom.hom.left x = y := by
  have comm (z : X'.obj.left) :=
    congrArg (fun k : X' ⟶ Y ↦ k.hom.left z) square
  obtain ⟨g, hg⟩ := transitive (a.hom.left x) (a.hom.left y)
    ((comm x).trans ((congrArg b.hom.left same_base).trans (comm y).symm))
  refine ⟨g, injective ?_⟩
  exact (congrArg (fun k : X' ⟶ X ↦ k.hom.left x) (equivariant g)).trans hg

/-- 概要：始域と基底を同時に被約化しても点の推移性が保たれる（論文 定理 3.1）。
方針：被約化の包含の自然性・同変性・点の単射性を正方形の比較に適用する。
規約：Noether 性と有限群性はこの幾何的な比較には不要。
使われ方：非被約な交わりを被約な基底に対する帰納へ戻す。 -/
theorem finiteTypeReductionAction_transitive_on_fibers {S : Scheme.{u}}
    {X Y : FiniteTypeSchemes S} {G : Type*} [Group G]
    (f : X ⟶ Y) (action : G →* Aut X)
    (transitive : ∀ x y : X.obj.left, f.hom.left x = f.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y) :
    ∀ x y : (finiteTypeReduction X).obj.left,
      (finiteTypeReductionMap f).hom.left x = (finiteTypeReductionMap f).hom.left y →
        ∃ g : G, (finiteTypeReductionAction action g).asIso.hom.hom.left x = y :=
  fiberTransitivity_of_injective_square f (finiteTypeReductionMap f)
    (finiteTypeReductionInclusion X) (finiteTypeReductionInclusion Y)
    (finiteTypeReductionMap_comp_inclusion f).symm action (finiteTypeReductionAction action)
    (finiteTypeReductionAction_comp_inclusion action)
    (finiteTypeReductionInclusion X).hom.left.isClosedEmbedding.injective transitive

/-- 概要：元の切断は両側の被約化後にも切断となる（論文 定理 3.1）。
方針：被約化関手を切断の恒等式に適用する。
規約：元の基底の被約性を要求せず、基底も被約化する。
使われ方：閉和の非被約な交わり上で切断の存在を帰納へ渡す。 -/
theorem finiteTypeReductionMap_section {S : Scheme.{u}} {X Y : FiniteTypeSchemes S}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    finiteTypeReductionMap s ≫ finiteTypeReductionMap f = 𝟙 (finiteTypeReduction Y) := by
  change (finiteTypeReductionFunctor S).map s ≫ (finiteTypeReductionFunctor S).map f =
    𝟙 ((finiteTypeReductionFunctor S).obj Y)
  rw [← Functor.map_comp, hs]
  exact (finiteTypeReductionFunctor S).map_id Y

/-- 概要：有限型の圏内の被約化は Krull 次元を保つ（論文 定理 3.1）。
方針：被約閉構造の台との同相と、全空間の部分型との同相を使う。
規約：Noether 性や有限次元は不要。
使われ方：交わりの有限な次元上界を両側の被約化後にも保持する。 -/
theorem finiteTypeReduction_dimension {S : Scheme.{u}} (X : FiniteTypeSchemes S) :
    topologicalKrullDim (finiteTypeReduction X).obj.left = topologicalKrullDim X.obj.left := by
  change topologicalKrullDim (reducedClosedSubscheme (⊤ : Closeds X.obj.left)) = _
  rw [reducedClosedSubscheme_dimension]
  change topologicalKrullDim (Set.univ : Set X.obj.left) = _
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X.obj.left).isHomeomorph

end SerrePositivity.KST.Descent
