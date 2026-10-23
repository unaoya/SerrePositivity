module

public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedTransportSquare
public import SerrePositivity.InfinityCategories.F1.Transport.InitialParametrizedPointTransport
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningPointFiberEvaluation

/-!
概要：可換正方形の普遍輸送の自然性を同じ指定点で評価し、端点の表示も正規化する。
方針：全 fiber の内部 Hom の比較を後合成し、前後合成と評価の厳密な可換式を使う。
規約：指定点は全空間の射による同じ像。始対象性は同値性の結論でだけ使う。
使われ方：Tw の恒等点輸送と、同じ Yoneda Hom 作用後の pointed-space 輸送の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 可換正方形の輸送の自然性は、同じ始点の点での評価も保つ。 -/
def parametrizedPointTransport_squareIso {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g) (a b : B _⦋0⦌)
    (v : (vertexFiber p a) _⦋0⦌) :
    FunctorIso
      (parametrizedFiberTransport p a b ≫ evaluateFunctorAt v ≫
        transportSquareFiberMap p q f g h b)
      (intervalMappingPost g a b ≫ parametrizedFiberTransport q (g.app _ a) (g.app _ b) ≫
        evaluateFunctorAt ((transportSquareFiberMap p q f g h a).app _ v)) := by
  have he := (parametrizedFiberTransport_squareIso p q f g h a b).postcomp
    (evaluateFunctorAt v)
  simpa only [Category.assoc, evaluateFunctorAt_post, evaluateFunctorAt_pre] using he

/-- 表示を変えない後合成は、元の区間後合成と厳密に一致する。 -/
lemma intervalMappingPostOfEq_refl {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    intervalMappingPostOfEq f x y rfl rfl = intervalMappingPost f x y := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingPostOfEq, intervalMappingUncurry_curryOfEndpoints,
    intervalMappingPost_universal_uncurry]

/-- 端点を別の表示に正規化しても、同じ指定点の輸送は一つの関手同型で比較できる。 -/
def parametrizedPointTransport_squareIsoOfEq {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g) (a b : B _⦋0⦌)
    (s t : D _⦋0⦌) (hs : g.app _ a = s) (ht : g.app _ b = t)
    (v : (vertexFiber p a) _⦋0⦌) (w : (vertexFiber q s) _⦋0⦌)
    (hw : f.app (Opposite.op ⦋0⦌) v.val = w.val) :
    FunctorIso
      (parametrizedFiberTransport p a b ≫ evaluateFunctorAt v ≫
        transportSquareFiberMap p q f g h b ≫ eqToHom (congrArg (vertexFiber q) ht))
      (intervalMappingPostOfEq g a b hs ht ≫ parametrizedFiberTransport q s t ≫
        evaluateFunctorAt w) := by
  subst s
  subst t
  have hvw : (transportSquareFiberMap p q f g h a).app (Opposite.op ⦋0⦌) v = w :=
    Subtype.ext hw
  subst w
  simpa only [eqToHom_refl, Category.comp_id, intervalMappingPostOfEq_refl] using
    parametrizedPointTransport_squareIso p q f g h a b v

/-- 始対象からの輸送と終点 fiber の同値を送ると、同じ指定点での正規化した輸送も同値。 -/
lemma parametrizedPointTransport_square_isQCatEquivalence_of_initial
    {E B F D : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g) (a b : B _⦋0⦌)
    (s t : D _⦋0⦌) (hs : g.app _ a = s) (ht : g.app _ b = t)
    (v : (vertexFiber p a) _⦋0⦌) (hv : IsInitialVertex v.val)
    (w : (vertexFiber q s) _⦋0⦌) (hw : f.app (Opposite.op ⦋0⦌) v.val = w.val)
    (hb : IsQCatEquivalence (transportSquareFiberMap p q f g h b)) :
    IsQCatEquivalence (intervalMappingPostOfEq g a b hs ht ≫
      parametrizedFiberTransport q s t ≫ evaluateFunctorAt w) := by
  have h₁ := parametrizedFiberTransport_evaluate_isQCatEquivalence_of_initialFiberPoint
    p a b v hv
  have h₂ := (qCatEquivalenceOfIso (eqToIso (congrArg (vertexFiber q) ht))).isQCatEquivalence
  exact (h₁.comp (hb.comp h₂)).ofFunctorIso
    (parametrizedPointTransport_squareIsoOfEq p q f g h a b s t hs ht v w hw)

end SerrePositivity.InfinityCategories
