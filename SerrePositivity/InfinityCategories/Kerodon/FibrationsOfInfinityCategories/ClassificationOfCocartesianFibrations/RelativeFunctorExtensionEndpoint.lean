module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChangeVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LiftEndpoint

/-!
概要：相対延長の空間から指定した制限を取り、引き戻した射への相対関手空間へ送る。
方針：延長の包含、制限、底の表示の移送、相対関手空間の底変換同型を合成する。
規約：具体的な延長の頂点での計算も保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な持ち上げから写像空間の射を作る選択の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：相対関手の制限は通常の射の相対頂点を前合成した射の相対頂点へ写す。
方針：部分型の内部 Hom 成分で計算する。
規約：元の射影の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対延長の指定した部分での評価。 -/
lemma relativeFunctorPre_vertex {A C E B : SSet.{u}} (p : E ⟶ B) (b : A ⟶ B)
    (j : C ⟶ A) (W : A ⟶ E) (hW : W ≫ p = b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b j).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b W hW) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (j ≫ b) (j ≫ W) (by rw [Category.assoc, hW]) := by
  apply Subtype.ext
  rfl

/-- 概要：相対延長の空間を指定した部分で評価し、引き戻しへの相対関手空間へ送る。
方針：制限した底の図式を同定し、底変換同型の逆射を合成する。
規約：j は最初に固定した部分図式の包含 i とは独立に指定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、選択空間の持ち上げの終点の写像空間への射。 -/
noncomputable def relativeFunctorExtensionEndpoint {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p b i v hv ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd p q) a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p b i v hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b j ≫
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p) hj) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p q a).inv

/-- 概要：具体的な相対延長の終点が引き戻しへの射 g を表すなら、選択空間の終点写像は g の相対頂点を返す。
方針：制限の頂点の計算、底の移送、底変換同型の逆射の計算を使う。
規約：j で制限した射と g の第一射影への合成の一致を仮定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、実際の持ち上げと相対写像空間の比較射の接続。 -/
lemma relativeFunctorExtensionEndpoint_vertex {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q)
    (W : A ⟶ E) (hW : W ≫ p = b) (hWi : i ≫ W = v)
    (g : C ⟶ pullback p q) (hg : g ≫ pullback.snd p q = a)
    (hWj : j ≫ W = g ≫ pullback.fst p q) :
    (relativeFunctorExtensionEndpoint p b i v hv j q a hj).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd p q) a g hg := by
  have ht : (j ≫ W) ≫ p = a ≫ q := by rw [Category.assoc, hW, hj]
  have hE : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p b i v hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b j).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (j ≫ b) (j ≫ W) (by rw [Category.assoc, hW]) :=
    relativeFunctorPre_vertex p b j W hW
  have hT := congrArg (fun z => (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p) hj)).app _ z) hE
  have hT' : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p b i v hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b j ≫
      eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p) hj)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (a ≫ q) (j ≫ W) ht :=
    hT.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex_transport p hj _ _)
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeBackward p q a).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (a ≫ q) (j ≫ W) ht) :=
      congrArg (fun z => ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeIso p q a).inv.app _).hom z) hT'
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd p q) a (pullback.lift (j ≫ W) a ht)
        (pullback.lift_snd _ _ _) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeBackward_vertex p q a _ ht
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd p q) a g hg := by
      apply Subtype.ext
      apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans hWj
      · exact (pullback.lift_snd _ _ _).trans hg.symm

/-- 概要：left anodyne な部分図式を固定する二つの延長の終点は、引き戻した射への相対写像空間内で同型。
方針：可縮な延長空間の二頂点の同型を終点へ写し、具体的な終点の計算で表示を揃える。
規約：底と最初に固定する部分図式は二つの延長で共通。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な変換の持ち上げの選択独立性。 -/
noncomputable def relativeFunctorExtensionEndpoint_witnessIso {A D C E F B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : A ⟶ B) (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q)
    (W W' : A ⟶ E) (hW : W ≫ p = b) (hW' : W' ≫ p = b)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⟶ pullback p q) (hg : g ≫ pullback.snd p q = a) (hg' : g' ≫ pullback.snd p q = a)
    (hWj : j ≫ W = g ≫ pullback.fst p q) (hWj' : j ≫ W' = g' ≫ pullback.fst p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd p q) a g hg)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (pullback.snd p q) a g' hg') := by
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩
  let y := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W', hW', hWi'⟩
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p b i hi v hv).vertexIso x y)
    (relativeFunctorExtensionEndpoint p b i v hv j q a hj)
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk
    (relativeFunctorExtensionEndpoint_vertex p b i v hv j q a hj W hW hWi g hg hWj))).symm ≪≫ e ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk
        (relativeFunctorExtensionEndpoint_vertex p b i v hv j q a hj W' hW' hWi' g' hg' hWj'))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
