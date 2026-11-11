module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberSquareHZero

/-! # D(S) の指定四辺による長完全列

概要：D3 の Hⁱ を用いて、引き戻し四角形の五項長完全列を与える。
方針：指定四辺の distinguished triangle の列を頂点のホモロジー比較で移す。
規約：第二射は B→D − C→D、零次では D5d の H⁰ の射。使われ方：Π2 の excision。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)

/-- 概要：中間二頂点の複体ホモロジーの直和を D3 の Hⁱ の直和へ同定する。
方針：各頂点の比較同型の逆の直和を取る。
規約：順序 B、C を保持する。使われ方：列の中央の項の比較。 -/
def derivedSquareInfinityMiddleIso (i : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).leftObj.homology i ⊞
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).rightObj.homology i ≅
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBVertex F) ⊞
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareCVertex F) :=
  biprod.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBVertex F)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareCVertex F)).symm

/-- 概要：D3 の Hⁱ による A、B⊕C、D の三項列。
方針：複体ホモロジーの列を頂点ごとの比較同型で移す。
規約：射は元の四辺の像。使われ方：長完全列の中央三項。 -/
def derivedSquareInfinityHomology₂ (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    ShortComplex (ModuleCat S) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedModuleShortComplexTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₂ F hF i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).symm
    (derivedSquareInfinityMiddleIso F i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).symm

/-- 概要：長完全列の第一射は下辺・左辺の Hⁱ の対である。
方針：辺の Hⁱ の比較式で共役した射を同定する。
規約：元の辺のホモトピー類の射を使う。使われ方：指定四辺の第一射の固定。 -/
lemma derivedSquareInfinityHomology₂_f (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (derivedSquareInfinityHomology₂ F hF i).f = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyPair F i := by
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyPair F i) ≫ (derivedSquareInfinityMiddleIso F i).hom := by
      change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₂ F hF i).f ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₂_f]
      exact (Category.assoc _ _ _).symm
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyPair F i ≫
        (derivedSquareInfinityMiddleIso F i).inv) ≫ (derivedSquareInfinityMiddleIso F i).hom :=
      congrArg (fun k => k ≫ (derivedSquareInfinityMiddleIso F i).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyPair_comparison F i).symm
    _ = _ := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：長完全列の第二射は右辺の Hⁱ から上辺の Hⁱ を引いた差である。
方針：二辺の Hⁱ の自然性で共役した差を同定する。
規約：紙上図式では右辺 − 下辺。使われ方：差の符号の固定。 -/
lemma derivedSquareInfinityHomology₂_g (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (derivedSquareInfinityHomology₂ F hF i).g = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyDifference F i := by
  calc
    _ = ((derivedSquareInfinityMiddleIso F i).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyDifference F i) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).inv := by
      change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₂ F hF i).g ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₂_g]
      exact (Category.assoc _ _ _).symm
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyDifference F i ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).hom) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).inv :=
      congrArg (fun k => k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).inv)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyDifference_comparison F i).symm
    _ = _ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：D3 の Hⁱ の接続準同型 Hⁱ(D) → Hʲ(A)。
方針：三角形の接続準同型を頂点の比較同型で移す。
規約：i+1=j、シフトとの整合は FiberConnectingShift の比較を共有する。
使われ方：D(S) の長完全列の接続射。 -/
def derivedSquareInfinityConnecting (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F)
    (i j : ℤ) (h : i + 1 = j) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomologyConnecting F hF i j h ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).inv

/-- 概要：D3 の Hⁱ による Dⁱ、Aʲ、Bʲ⊕Cʲ の三項列。
方針：接続射の後の複体ホモロジーの列を比較同型で移す。
規約：i+1=j。使われ方：A の項の完全性。 -/
def derivedSquareInfinityHomology₁ (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    ShortComplex (ModuleCat S) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedModuleShortComplexTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₁ F hF i j h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).symm
    (derivedSquareInfinityMiddleIso F j)

/-- 概要：D3 の Hⁱ による Bⁱ⊕Cⁱ、Dⁱ、Aʲ の三項列。
方針：接続射の前の複体ホモロジーの列を比較同型で移す。
規約：i+1=j。使われ方：D の項の完全性。 -/
def derivedSquareInfinityHomology₃ (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i j : ℤ) (h : i + 1 = j) :
    ShortComplex (ModuleCat S) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedModuleShortComplexTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₃ F hF i j h)
    (derivedSquareInfinityMiddleIso F i)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTargetVertex F)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso S j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).symm

/-- 概要：接続射の後の列の射は接続射と二辺の対である。
方針：定義と中央三項の第一射の同定を用いる。
規約：i+1=j。使われ方：五項列の左側の接続。 -/
lemma derivedSquareInfinityHomology₁_maps (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F)
    (i j : ℤ) (h : i + 1 = j) :
    (derivedSquareInfinityHomology₁ F hF i j h).f = derivedSquareInfinityConnecting F hF i j h ∧
      (derivedSquareInfinityHomology₁ F hF i j h).g = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyPair F j :=
  ⟨rfl, derivedSquareInfinityHomology₂_f F hF j⟩

/-- 概要：接続射の前の列の射は二辺の差と接続射である。
方針：定義と中央三項の第二射の同定を用いる。
規約：i+1=j。使われ方：五項列の右側の接続。 -/
lemma derivedSquareInfinityHomology₃_maps (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F)
    (i j : ℤ) (h : i + 1 = j) :
    (derivedSquareInfinityHomology₃ F hF i j h).f = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareInfinityHomologyDifference F i ∧
      (derivedSquareInfinityHomology₃ F hF i j h).g = derivedSquareInfinityConnecting F hF i j h :=
  ⟨derivedSquareInfinityHomology₂_g F hF i, rfl⟩

/-- 概要：D(S) の Hⁱ の長完全列は三つの位置で完全である。
方針：複体ホモロジーの長完全列を頂点ごとの同型で移す。
規約：Hⁱ⁻¹(D) → Hⁱ(A) → Hⁱ(B)⊕Hⁱ(C) → Hⁱ(D) → Hⁱ⁺¹(A)。
使われ方：Π2 の一般的な excision の完全性。 -/
theorem derivedSquareInfinityHomologyLongExact (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) (i : ℤ) :
    (derivedSquareInfinityHomology₁ F hF (i - 1) i (by omega)).Exact ∧
      (derivedSquareInfinityHomology₂ F hF i).Exact ∧
        (derivedSquareInfinityHomology₃ F hF i (i + 1) rfl).Exact := by
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedModuleShortComplexTransport_exact _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₁_exact F hF _ _ _)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedModuleShortComplexTransport_exact _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₂_exact F hF i)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedModuleShortComplexTransport_exact _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHomology₃_exact F hF _ _ _)

/-- 概要：零次で長完全列の第一射は D5d の元の二辺の H⁰ の対である。
方針：全次数の計算式を零次で評価する。
規約：D5d の同じ関手を用いる。使われ方：Π2 の離散入力の短完全列。 -/
lemma derivedSquareInfinityHomology₂_f_zero (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    (derivedSquareInfinityHomology₂ F hF 0).f = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHZeroPair F :=
  derivedSquareInfinityHomology₂_f F hF 0

/-- 概要：零次で長完全列の第二射は D5d の元の二辺の H⁰ の差である。
方針：全次数の計算式を零次で評価する。
規約：紙上の右辺 − 下辺。使われ方：Π2 の差の全射性と環の引き戻し。 -/
lemma derivedSquareInfinityHomology₂_g_zero (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    (derivedSquareInfinityHomology₂ F hF 0).g = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareHZeroDifference F :=
  derivedSquareInfinityHomology₂_g F hF 0

end SerrePositivity.InfinityCategories.Project.DerivedCategories
