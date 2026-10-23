module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationMap
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChangeVertices

/-!
概要：coherent な変換の具体的な prism の持ち上げと可縮な選択空間の接続。
方針：持ち上げを curry し、相対始点評価の fiber の頂点へ移す。
規約：始点と底の prism を厳密に固定した持ち上げを入力とする。
使われ方：Kerodon Lemma 5.2.2.13、unstraightening の恒等・合成の整合性の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対 lift の終点写像は通常の lift の頂点で終点評価となる。
方針：fiber の頂点表示と内部 Hom の後合成を計算する。
規約：元の射 p の充填性は不要。
使われ方：Kerodon Lemma 5.2.2.13、具体的な持ち上げの終点の比較。 -/
lemma relativeEdgeLiftSpaceEndpoint_vertex {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p)
    (Q : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (hQ : Q ≫ relativeEdgeSource p = c) :
    (relativeEdgeLiftSpaceEndpoint p c).app _
      (relativeEdgeLiftSpaceVertexEquiv p c ⟨Q, hQ⟩) =
    relativeFunctorVertex p (c ≫ pullback.snd p
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (by
        rw [Category.assoc, relativeEdgeEndpoint_comp, ← Category.assoc, hQ]) := by
  apply Subtype.ext
  rfl

/-- 概要：相対 lift の具体的な終点を、引き戻した射への相対関手頂点として回収する。
方針：終点の頂点の計算と相対関手空間の底変換の逆射の計算を合成する。
規約：すべて一般の単体集合の射について計算する。
使われ方：Kerodon Remark 5.6.2.5、unstraightening の具体的な持ち上げの終点。 -/
lemma relativeEdgeLiftSpaceEndpoint_baseChange_vertex {A X B D : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ relativeEdgeSourceTarget p)
    (Q : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (hQ : Q ≫ relativeEdgeSource p = c)
    (G : D ⟶ B) (a : A ⟶ D)
    (he : c ≫ pullback.snd p
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = a ≫ G)
    (g : A ⟶ pullback p G) (hg : g ≫ pullback.snd p G = a)
    (hQg : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      g ≫ pullback.fst p G) :
    (relativeEdgeLiftSpaceEndpoint p c ≫ eqToHom (congrArg (relativeFunctorSpace p) he) ≫
      (relativeFunctorBaseChangeIso p G a).inv).app _
        (relativeEdgeLiftSpaceVertexEquiv p c ⟨Q, hQ⟩) =
      relativeFunctorVertex (pullback.snd p G) a g hg := by
  let ev := evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have ht : (Q ≫ ev) ≫ p = a ≫ G := by
    rw [Category.assoc, relativeEdgeEndpoint_comp, ← Category.assoc, hQ, he]
  have hE := relativeEdgeLiftSpaceEndpoint_vertex p c Q hQ
  have hT := congrArg (fun z => (eqToHom (congrArg (relativeFunctorSpace p) he)).app _ z) hE
  have hT' : (relativeEdgeLiftSpaceEndpoint p c ≫
      eqToHom (congrArg (relativeFunctorSpace p) he)).app _
        (relativeEdgeLiftSpaceVertexEquiv p c ⟨Q, hQ⟩) =
      relativeFunctorVertex p (a ≫ G) (Q ≫ ev) ht :=
    hT.trans (relativeFunctorVertex_transport p he _ _)
  calc
    _ = (relativeFunctorBaseChangeBackward p G a).app _
        (relativeFunctorVertex p (a ≫ G) (Q ≫ ev) ht) :=
      congrArg (fun z => ((relativeFunctorBaseChangeIso p G a).inv.app _).hom z) hT'
    _ = relativeFunctorVertex (pullback.snd p G) a (pullback.lift (Q ≫ ev) a ht)
        (pullback.lift_snd _ _ _) := relativeFunctorBaseChangeBackward_vertex p G a _ ht
    _ = relativeFunctorVertex (pullback.snd p G) a g hg := by
      apply Subtype.ext
      apply congrArg functorVertex
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans hQg
      · exact (pullback.lift_snd _ _ _).trans hg.symm

/-- 概要：coherent な変換の具体的な prism の持ち上げは選択空間の頂点を与える。
方針：curry した持ち上げが相対始点図式の上にあることを二つの射影で確認する。
規約：始点・底・変換は入力の等式のまま固定する。
使われ方：Kerodon Lemma 5.2.2.13、任意の具体的な持ち上げと選択した射の比較。 -/
noncomputable def leftUnstraighteningTransformationWitness
    {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u})
    (hW₀ : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F)
    (hWp : W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H) :
    (leftUnstraighteningTransformationChoiceSpace F H h₀) _⦋0⦌ :=
  relativeEdgeLiftSpaceVertexEquiv pointedSpaceProjection
    (leftUnstraighteningTransformationSource F H h₀) ⟨curry W, by
      apply pullback.hom_ext
      · simp only [relativeEdgeSource, leftUnstraighteningTransformationSource,
          Category.assoc, pullback.lift_fst, curry_evaluateFunctorAt_interval, hW₀]
      · simp only [relativeEdgeSource, leftUnstraighteningTransformationSource,
          Category.assoc, pullback.lift_snd, ← curry_natural_right, hWp]⟩

/-- 概要：具体的な prism の持ち上げの終点は、選択空間の終点写像で得る相対関手と一致する。
方針：相対 lift の終点の計算と底変換の頂点での計算を使う。
規約：底上の射 g と具体的な持ち上げの終点の一致を仮定する。
使われ方：Kerodon Corollary 5.6.0.6、恒等・合成の具体的な持ち上げとの比較。 -/
lemma leftUnstraighteningTransformationWitness_endpoint
    {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ B ⟶ SpaceInfinity.{u})
    (h₀ : prismEndpoint 0 B ≫ H = F) (h₁ : prismEndpoint 1 B ≫ H = G)
    (W : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u})
    (hW₀ : prismEndpoint 0 _ ≫ W = pullback.fst pointedSpaceProjection F)
    (hWp : W ≫ pointedSpaceProjection = (Δ[1] ◁ leftUnstraighteningProjection F) ≫ H)
    (g : leftUnstraightening F ⟶ leftUnstraightening G)
    (hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (hW₁ : prismEndpoint 1 _ ≫ W = g ≫ pullback.fst pointedSpaceProjection G) :
    (leftUnstraighteningTransformationEndpoint F G H h₀ h₁).app _
      (leftUnstraighteningTransformationWitness F H h₀ W hW₀ hWp) =
      relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        g hg := by
  exact relativeEdgeLiftSpaceEndpoint_baseChange_vertex pointedSpaceProjection
    (leftUnstraighteningTransformationSource F H h₀) (curry W) (by
      apply pullback.hom_ext
      · simp only [relativeEdgeSource, leftUnstraighteningTransformationSource,
          Category.assoc, pullback.lift_fst, curry_evaluateFunctorAt_interval, hW₀]
      · simp only [relativeEdgeSource, leftUnstraighteningTransformationSource,
          Category.assoc, pullback.lift_snd, ← curry_natural_right, hWp])
    G (leftUnstraighteningProjection F)
    (leftUnstraighteningTransformationSource_endpoint F G H h₀ h₁) g hg (by
      rw [curry_evaluateFunctorAt_interval, hW₁])

end SerrePositivity.InfinityCategories
