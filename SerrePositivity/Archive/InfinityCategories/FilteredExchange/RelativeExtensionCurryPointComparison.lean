module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorCurryIsoFiberRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionCurryComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackTransport

/-!
概要：既存の持ち上げの終点の指定比較を curry して評価しても元の同じ制限となる。
方針：引き戻し表示後の元の指定同型に相対 curry の成分比較を適用する。
規約：元の二つの延長と指定同型を保持。使われ方：元の三角形比較の各点への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A D C E F B L : SSet.{u}} [Quasicategory L]
  (p : E ⟶ B) [LeftFibration p] (d : A ⟶ B) (i : D ⟶ A)
  (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ d)
  (j : C ⊗ L ⟶ A) (q : F ⟶ B) (a : C ⟶ F)
  (hj : j ≫ d = (fst C L ≫ a) ≫ q)
  (W W' : A ⟶ E) (hW : W ≫ p = d) (hW' : W' ≫ p = d)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
  (g g' : C ⊗ L ⟶ pullback p q)
  (hg : g ≫ pullback.snd p q = fst C L ≫ a)
  (hg' : g' ≫ pullback.snd p q = fst C L ≫ a)
  (hWj : j ≫ W = g ≫ pullback.fst p q)
  (hWj' : j ≫ W' = g' ≫ pullback.fst p q)

/-- 既存の指定 curry 終点比較の成分は元の二延長からの同じ比較の制限。 -/
lemma relativeExtensionEndpoint_curryIso_app (l : L _⦋0⦌) :
    HEq
      ((relativeFunctorExtensionEndpoint_curryIso p d i hi v hv j q a hj
        W W' hW hW' hWi hWi' g g' hg hg' hWj hWj').app l)
      (VertexIso.map
        (relativeFunctorExtensionEndpoint_witnessIso p d i hi v hv j q (fst C L ≫ a) hj
          W W' hW hW' hWi hWi' g g' hg hg' hWj hWj')
        (relativeFunctorPre (pullback.snd p q) (fst C L ≫ a)
          (lift (𝟙 C) (SSet.const l)))) :=
  relativeFunctorCurryIso_app (pullback.snd p q) a g g' hg hg' _ l

/-- 元の指定 curry 終点比較の成分を始域へ制限しても同じ指定比較の直接制限。 -/
lemma relativeExtensionEndpoint_curryIso_app_pre {C' : SSet.{u}}
    (l : L _⦋0⦌) (s : C' ⟶ C) :
    HEq
      (VertexIso.map
        ((relativeFunctorExtensionEndpoint_curryIso p d i hi v hv j q a hj
          W W' hW hW' hWi hWi' g g' hg hg' hWj hWj').app l)
        (relativeFunctorPre (pullback.snd p q) a s))
      (VertexIso.map
        (relativeFunctorExtensionEndpoint_witnessIso p d i hi v hv j q (fst C L ≫ a) hj
          W W' hW hW' hWi hWi' g g' hg hg' hWj hWj')
        (relativeFunctorPre (pullback.snd p q) (fst C L ≫ a)
          (s ≫ lift (𝟙 C) (SSet.const l)))) :=
  relativeFunctorCurryIso_app_pre (pullback.snd p q) a g g' hg hg' _ l s

end SerrePositivity.InfinityCategories.F2
