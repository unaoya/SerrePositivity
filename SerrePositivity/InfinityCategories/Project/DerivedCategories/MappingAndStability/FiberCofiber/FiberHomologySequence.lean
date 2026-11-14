module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FiberSquareTriangle
public import Mathlib.Algebra.Homology.Additive

/-! # 指定四辺の fiber 列の長完全列

概要：引き戻し四角形から Hⁱ⁻¹(D) → Hⁱ(A) → Hⁱ(B) ⊕ Hⁱ(C) → Hⁱ(D) → Hⁱ⁺¹(A) を作る。
方針：指定四辺の distinguished triangle の長完全列を、複体ホモロジーと二項直和の比較で移す。
規約：中央の差は B→D − C→D（Core の右辺 − 上辺、紙上図式の右辺 − 下辺）。使われ方：Π2 の excision から通常の加群の完全列を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded Pretriangulated
open scoped _root_.Simplicial
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
variable {S : Type u} [CommRing S]

/-- 概要：短複体を三つの対象の同型に沿って移す。
方針：射を同型で共役し、連続する合成の零性を移す。
規約：加群の短複体。使われ方：長完全列の各三項の具体化。 -/
def derivedModuleShortComplexTransport (K : ShortComplex (ModuleCat S))
    {A B C : ModuleCat S} (e₁ : K.X₁ ≅ A) (e₂ : K.X₂ ≅ B) (e₃ : K.X₃ ≅ C) :
    ShortComplex (ModuleCat S) :=
  ShortComplex.mk (e₁.inv ≫ K.f ≫ e₂.hom) (e₂.inv ≫ K.g ≫ e₃.hom) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc K.f K.g e₃.hom, K.zero, zero_comp, comp_zero])

/-- 概要：同型に沿って移した短複体は元と同型である。
方針：三つの同型を短複体の同型の成分に使う。
規約：共役した射の可換性を含む。使われ方：完全性の移送。 -/
def derivedModuleShortComplexTransportIso (K : ShortComplex (ModuleCat S))
    {A B C : ModuleCat S} (e₁ : K.X₁ ≅ A) (e₂ : K.X₂ ≅ B) (e₃ : K.X₃ ≅ C) :
    K ≅ derivedModuleShortComplexTransport K e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃
    (by simp [derivedModuleShortComplexTransport])
    (by simp [derivedModuleShortComplexTransport])

/-- 概要：短複体の完全性は三対象の同型による移送で保たれる。
方針：短複体の同型不変性を使う。
規約：完全性の追加仮定は元の短複体だけ。使われ方：長完全列の三項完全性。 -/
lemma derivedModuleShortComplexTransport_exact (K : ShortComplex (ModuleCat S))
    {A B C : ModuleCat S} (e₁ : K.X₁ ≅ A) (e₂ : K.X₂ ≅ B) (e₃ : K.X₃ ≅ C)
    (hK : K.Exact) : (derivedModuleShortComplexTransport K e₁ e₂ e₃).Exact :=
  ShortComplex.exact_of_iso (derivedModuleShortComplexTransportIso K e₁ e₂ e₃) hK

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)

/-- 概要：各次数で指定した下辺・左辺のホモロジー射の対。
方針：二つの元の辺のホモロジー射を二項直和へ持ち上げる。
規約：成分の順は B、C。使われ方：長完全列の A からの射。 -/
def derivedSquareHomologyPair (i : ℤ) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareCornerComplex F).homology i ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj.homology i ⊞
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj.homology i :=
  biprod.lift (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap F) i)
    (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap F) i)

/-- 概要：各次数で指定した右辺と上辺のホモロジー射の差。
方針：直和の第一成分に右辺、第二成分に上辺の負を置く。
規約：右辺 − 上辺。使われ方：長完全列の D への射。 -/
def derivedSquareHomologyDifference (i : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj.homology i ⊞
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj.homology i ⟶
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).targetObj.homology i :=
  biprod.desc (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap i)
    (-HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap i)

/-- 概要：三角形の第一頂点の導来ホモロジーを元の複体のホモロジーと同定する。
方針：局所化関手のホモロジー比較を評価する。
規約：任意の整数次数。使われ方：長完全列の A の項。 -/
def derivedSquareCornerHomologyIso (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).obj₁ ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareCornerComplex F).homology i :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareCornerComplex F)

/-- 概要：三角形の中央のホモロジーを二頂点のホモロジーの直和へ同定する。
方針：局所化の比較と加法的ホモロジー関手の直和比較を合成する。
規約：順序 B、C を保持する。使われ方：長完全列の中央の項。 -/
def derivedSquareMiddleHomologyIso (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).obj₂ ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj.homology i ⊞
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj.homology i :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj ⊞ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) i).mapBiprod _ _

/-- 概要：三角形の終頂点の導来ホモロジーを元の終域のホモロジーと同定する。
方針：局所化関手のホモロジー比較を評価する。
規約：任意の整数次数。使われ方：長完全列の D の項。 -/
def derivedSquareTargetHomologyIso (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).obj₃ ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).targetObj.homology i :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation
    F).targetObj

/-- 概要：三角形の第一射のホモロジーは指定二辺の対と両立する。
方針：局所化の比較の自然性と直和への lift の保存を用いる。
規約：第一射を別の射に取り替えない。使われ方：長完全列の射の同定。 -/
lemma derivedSquareHomologyPair_comparison (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₁ ≫
      (derivedSquareMiddleHomologyIso F hF i).hom =
        (derivedSquareCornerHomologyIso F hF i).hom ≫ derivedSquareHomologyPair F i := by
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).hom.naturality
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePairMap F)
  change (DerivedCategory.homologyFunctor (ModuleCat S) i).map
    (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePairMap F)) ≫ _ = _ at hn
  calc
    _ = ((DerivedCategory.homologyFunctor (ModuleCat S) i).map
        (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePairMap F)) ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app _).hom) ≫
          ((HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) i).mapBiprod _ _).hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫
      ((HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) i).mapBiprod _ _).hom) hn
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (fun k => (derivedSquareCornerHomologyIso F hF i).hom ≫ k)
      (biprod.map_lift_mapBiprod (HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) i)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomMap F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftMap F))

/-- 概要：三角形の第二射のホモロジーは指定二辺の差と両立する。
方針：直和からの desc の保存と局所化の比較の自然性を用いる。
規約：右辺 − 上辺の負号を保持する。使われ方：長完全列の射の同定。 -/
lemma derivedSquareHomologyDifference_comparison (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₂ ≫
      (derivedSquareTargetHomologyIso F hF i).hom =
        (derivedSquareMiddleHomologyIso F hF i).hom ≫ derivedSquareHomologyDifference F i := by
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).hom.naturality
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap)
  change (DerivedCategory.homologyFunctor (ModuleCat S) i).map
    (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference _ _)) ≫ _ = _ at hn
  calc
    _ = ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj ⊞ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj)).hom ≫
          (HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) i).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap) := hn
    _ = _ := by
      have hh := biprod.mapBiprod_hom_desc
        (HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) i)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftMap (-(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightMap)
      simp only [Functor.map_neg] at hh
      exact (congrArg (fun k =>
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj ⊞ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj)).hom ≫ k)
          hh.symm).trans (Category.assoc _ _ _).symm

/-- 概要：指定四辺の三角形から得る接続準同型。
方針：Mathlib の接続準同型を二端点のホモロジー比較で共役する。
規約：i+1=j。使われ方：長完全列の次数を一つ上げる射。 -/
def derivedSquareHomologyConnecting (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F)
    (i j : ℤ) (h : i + 1 = j) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).targetObj.homology i ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareCornerComplex F).homology
      j :=
  (derivedSquareTargetHomologyIso F hF i).inv ≫
    DerivedCategory.HomologySequence.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF) i j h ≫
      (derivedSquareCornerHomologyIso F hF j).hom

/-- 概要：導来三角形のホモロジーの中央三項。
方針：二つの射の合成が零であることを distinguished 性から得る。
規約：まだ局所化側のホモロジー。使われ方：具体的な長完全列への移送。 -/
def derivedSquareDerivedHomology₂ (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    ShortComplex (ModuleCat S) :=
  ShortComplex.mk
    ((DerivedCategory.homologyFunctor (ModuleCat S) i).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₁)
    ((DerivedCategory.homologyFunctor (ModuleCat S) i).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₂)
    (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle_distinguished F hF), Functor.map_zero])

/-- 概要：長完全列の A、B⊕C、D の三項を具体的な加群で与える。
方針：導来三角形の中央三項を三つの比較同型で移送する。
規約：射は指定二辺の対・差。使われ方：長完全列の中央の完全性。 -/
def derivedSquareHomology₂ (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) : ShortComplex (ModuleCat S) :=
  derivedModuleShortComplexTransport (derivedSquareDerivedHomology₂ F hF i)
    (derivedSquareCornerHomologyIso F hF i) (derivedSquareMiddleHomologyIso F hF i)
    (derivedSquareTargetHomologyIso F hF i)

/-- 概要：中央三項の第一射は指定二辺のホモロジー射の対である。
方針：第一射の比較式で共役を消す。
規約：全整数次数。使われ方：H⁰ と元の二辺の整合。 -/
lemma derivedSquareHomology₂_f (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (derivedSquareHomology₂ F hF i).f = derivedSquareHomologyPair F i := by
  change (derivedSquareCornerHomologyIso F hF i).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₁ ≫
      (derivedSquareMiddleHomologyIso F hF i).hom = _
  rw [derivedSquareHomologyPair_comparison, Iso.inv_hom_id_assoc]

/-- 概要：中央三項の第二射は指定二辺のホモロジー射の差である。
方針：第二射の比較式で共役を消す。
規約：右辺 − 上辺。使われ方：差の符号の固定。 -/
lemma derivedSquareHomology₂_g (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (derivedSquareHomology₂ F hF i).g = derivedSquareHomologyDifference F i := by
  change (derivedSquareMiddleHomologyIso F hF i).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₂ ≫
      (derivedSquareTargetHomologyIso F hF i).hom = _
  rw [derivedSquareHomologyDifference_comparison, Iso.inv_hom_id_assoc]

/-- 概要：長完全列の中央の三項は完全である。
方針：distinguished triangle の中央の完全性を三つの同型で移す。
規約：IsPullbackSquare F 以外の整合仮定なし。使われ方：excision の中央完全性。 -/
theorem derivedSquareHomology₂_exact (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (derivedSquareHomology₂ F hF i).Exact :=
  derivedModuleShortComplexTransport_exact _ _ _ _
    (DerivedCategory.HomologySequence.exact₂ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle_distinguished F hF) i)

/-- 概要：接続射の後の三項 Dⁱ → Aʲ → Bʲ⊕Cʲ。
方針：導来三角形の接続射と第一射の短複体を同型で移す。
規約：i+1=j。使われ方：A の項での完全性。 -/
def derivedSquareHomology₁ (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    ShortComplex (ModuleCat S) :=
  derivedModuleShortComplexTransport
    (ShortComplex.mk (DerivedCategory.HomologySequence.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF) i j h)
      ((DerivedCategory.homologyFunctor (ModuleCat S) j).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₁)
      (DerivedCategory.HomologySequence.δ_comp _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle_distinguished F hF)
        i j h))
    (derivedSquareTargetHomologyIso F hF i) (derivedSquareCornerHomologyIso F hF j)
    (derivedSquareMiddleHomologyIso F hF j)

/-- 概要：接続射の後の短複体の第一射は指定した接続射である。
方針：定義を評価する。規約：i+1=j。使われ方：長完全列の隣接項の接続。 -/
lemma derivedSquareHomology₁_f (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    (derivedSquareHomology₁ F hF i j h).f = derivedSquareHomologyConnecting F hF i j h := rfl

/-- 概要：接続射の後の短複体の第二射は二辺の対である。
方針：中央三項の同じ射の同定を使う。
規約：i+1=j。使われ方：長完全列の A からの射。 -/
lemma derivedSquareHomology₁_g (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    (derivedSquareHomology₁ F hF i j h).g = derivedSquareHomologyPair F j :=
  derivedSquareHomology₂_f F hF j

/-- 概要：長完全列は A の項で完全である。
方針：distinguished triangle の接続射の後の完全性を移す。
規約：i+1=j。使われ方：Hⁱ⁻¹(D) → Hⁱ(A) → Hⁱ(B)⊕Hⁱ(C)。 -/
theorem derivedSquareHomology₁_exact (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    (derivedSquareHomology₁ F hF i j h).Exact :=
  derivedModuleShortComplexTransport_exact _ _ _ _
    (DerivedCategory.HomologySequence.exact₁ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle_distinguished F hF) i
      j h)

/-- 概要：接続射の前の三項 Bⁱ⊕Cⁱ → Dⁱ → Aʲ。
方針：導来三角形の第二射と接続射の短複体を同型で移す。
規約：i+1=j。使われ方：D の項での完全性。 -/
def derivedSquareHomology₃ (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    ShortComplex (ModuleCat S) :=
  derivedModuleShortComplexTransport
    (ShortComplex.mk
      ((DerivedCategory.homologyFunctor (ModuleCat S) i).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₂)
      (DerivedCategory.HomologySequence.δ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF) i j h)
      (DerivedCategory.HomologySequence.comp_δ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle_distinguished F hF)
        i j h))
    (derivedSquareMiddleHomologyIso F hF i) (derivedSquareTargetHomologyIso F hF i)
    (derivedSquareCornerHomologyIso F hF j)

/-- 概要：接続射の前の短複体の第一射は二辺の差である。
方針：中央三項の同じ射の同定を使う。
規約：右辺 − 上辺。使われ方：長完全列の D への射。 -/
lemma derivedSquareHomology₃_f (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    (derivedSquareHomology₃ F hF i j h).f = derivedSquareHomologyDifference F i :=
  derivedSquareHomology₂_g F hF i

/-- 概要：接続射の前の短複体の第二射は指定した接続射である。
方針：定義を評価する。規約：i+1=j。使われ方：長完全列の隣接項の接続。 -/
lemma derivedSquareHomology₃_g (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    (derivedSquareHomology₃ F hF i j h).g = derivedSquareHomologyConnecting F hF i j h := rfl

/-- 概要：長完全列は D の項で完全である。
方針：distinguished triangle の接続射の前の完全性を移す。
規約：i+1=j。使われ方：Hⁱ(B)⊕Hⁱ(C) → Hⁱ(D) → Hⁱ⁺¹(A)。 -/
theorem derivedSquareHomology₃_exact (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    (derivedSquareHomology₃ F hF i j h).Exact :=
  derivedModuleShortComplexTransport_exact _ _ _ _
    (DerivedCategory.HomologySequence.exact₃ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle_distinguished F hF) i
      j h)

/-- 概要：引き戻し四角形の五項の長完全列の三つの位置で完全性が成り立つ。
方針：三角形の各位置の完全性を連結する。
規約：全整数次数、指定二辺の対と右辺 − 上辺の差。使われ方：Π2 の excision の長完全列。 -/
theorem derivedSquareHomologyLongExact (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (derivedSquareHomology₁ F hF (i - 1) i (by omega)).Exact ∧
      (derivedSquareHomology₂ F hF i).Exact ∧
        (derivedSquareHomology₃ F hF i (i + 1) rfl).Exact :=
  ⟨derivedSquareHomology₁_exact F hF _ _ _, derivedSquareHomology₂_exact F hF i,
    derivedSquareHomology₃_exact F hF _ _ _⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
