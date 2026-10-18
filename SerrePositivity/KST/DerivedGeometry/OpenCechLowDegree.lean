module

public import SerrePositivity.KST.DerivedGeometry.SheafCoverExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
概要：実際の Čech の第0・第1項を被覆と二重交叉の切断へ比較する。
方針：Fin 1 と Fin 2 からの関数を被覆元と順序対へ同一視する。
規約：同型は Mathlib の Čech の積そのものから構成する。
使われ方：TT §3・§8、Toën §3.2 の Čech 増大と層条件の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w a b
open CategoryTheory Limits Preadditive TopologicalSpace Simplicial
namespace SerrePositivity.KST.DerivedGeometry
variable {X : TopCat.{w}} {ι : Type w} (U : ι → Opens X)

/--
概要：二つの開集合の Fin 2 添字の積は二項交叉に等しい。
方針：積の射影と交叉からの標準の錐で両側の包含を示す。
規約：積は Čech の実際の選ばれた積。
使われ方：TT §3、Toën §3.2 の Čech 第1項。
-/
lemma openFinTwoProduct_eq (t : Fin 2 → ι) :
    (∏ᶜ (U ∘ t)) = U (t 0) ⊓ U (t 1) := by
  apply le_antisymm
  · exact le_inf (leOfHom (Pi.π (U ∘ t) 0)) (leOfHom (Pi.π (U ∘ t) 1))
  · exact leOfHom (Pi.lift (fun k => homOfLE (by
      fin_cases k
      · exact inf_le_left
      · exact inf_le_right)))

/--
概要：Čech 第0項の形式的余積は元の被覆族と同型。
方針：一元添字の関数と一元積の同型を使う。
規約：評価前の形式的余積の同型。
使われ方：TT §3、Toën §3.2 の増大の零次数。
-/
def openCechZeroFormalIso :
    (FormalCoproduct.mk ι U).cech.obj (.op ⦋0⦌) ≅ FormalCoproduct.mk ι U := by
  letI : Unique (ToType ⦋0⦌) := inferInstanceAs (Unique (Fin 1))
  exact FormalCoproduct.isoOfComponents (Equiv.funUnique (Fin 1) ι)
    (fun t => productUniqueIso (U ∘ t))

/--
概要：Čech 第1項の形式的余積は順序対で添字づけた二重交叉と同型。
方針：Fin 2 の関数と順序対の同値および積と交叉の等式を使う。
規約：対角成分も保持する。
使われ方：TT §3・§8、Toën §3.2 の二つの制限写像。
-/
def openCechOneFormalIso :
    (FormalCoproduct.mk ι U).cech.obj (.op ⦋1⦌) ≅
      FormalCoproduct.mk (ι × ι) (fun p => U p.1 ⊓ U p.2) :=
  FormalCoproduct.isoOfComponents (finTwoArrowEquiv ι)
    (fun t => eqToIso (openFinTwoProduct_eq U t))

/--
概要：二重交叉から右側の被覆元への制限を形式的余積で表す。
方針：順序対の第2成分と交叉の射影を使う。
規約：評価後に通常の右制限となる射を固定する。
使われ方：TT §3、Toën §3.2 の Čech 第0余面。
-/
def openPairRightRestriction :
    FormalCoproduct.mk (ι × ι) (fun p => U p.1 ⊓ U p.2) ⟶
      FormalCoproduct.mk ι U :=
  ⟨Prod.snd, fun _ => homOfLE inf_le_right⟩

/--
概要：二重交叉から左側の被覆元への制限を形式的余積で表す。
方針：順序対の第1成分と交叉の射影を使う。
規約：評価後に通常の左制限となる射を固定する。
使われ方：TT §3、Toën §3.2 の Čech 第1余面。
-/
def openPairLeftRestriction :
    FormalCoproduct.mk (ι × ι) (fun p => U p.1 ⊓ U p.2) ⟶
      FormalCoproduct.mk ι U :=
  ⟨Prod.fst, fun _ => homOfLE inf_le_left⟩

/--
概要：第0面は同じ比較同型のもとで右制限となる。
方針：添字を計算し、開集合の射の一意性を使う。
規約：評価前の形式的余積での等式。
使われ方：TT §3、Toën §3.2 の Čech 微分比較。
-/
lemma openCech_zeroFace :
    (openCechOneFormalIso U).inv ≫
      (FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ (0 : Fin 2)).op ≫
        (openCechZeroFormalIso U).hom = openPairRightRestriction U := by
  exact FormalCoproduct.hom_ext rfl (fun _ => Subsingleton.elim _ _)

/--
概要：第1面は同じ比較同型のもとで左制限となる。
方針：添字を計算し、開集合の射の一意性を使う。
規約：評価前の形式的余積での等式。
使われ方：TT §3、Toën §3.2 の Čech 微分比較。
-/
lemma openCech_oneFace :
    (openCechOneFormalIso U).inv ≫
      (FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ (1 : Fin 2)).op ≫
        (openCechZeroFormalIso U).hom = openPairLeftRestriction U := by
  exact FormalCoproduct.hom_ext rfl (fun _ => Subsingleton.elim _ _)

variable {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{w} A]
  (P : (Opens X)ᵒᵖ ⥤ A)

/--
概要：Čech 第0項は被覆元上の切断の積と同型。
方針：形式的余積の第0項の比較を同じ前層で評価する。
規約：実際の Čech 複体の対象を用いる。
使われ方：TT §3、Toën §3.2 の増大。
-/
def openCechZeroIso : ((cechComplexFunctor U).obj P).X 0 ≅
    TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens P U :=
  (((FormalCoproduct.evalOp (Opens X) A).obj P).mapIso (openCechZeroFormalIso U).op).symm

/--
概要：Čech 第1項は二重交叉上の切断の積と同型。
方針：形式的余積の第1項の比較を同じ前層で評価する。
規約：対角成分と順序対の両方を保持する。
使われ方：TT §3・§8、Toën §3.2 の層条件との比較。
-/
def openCechOneIso : ((cechComplexFunctor U).obj P).X 1 ≅
    TopCat.Presheaf.SheafConditionEqualizerProducts.piInters P U :=
  (((FormalCoproduct.evalOp (Opens X) A).obj P).mapIso (openCechOneFormalIso U).op).symm

/--
概要：Čech の最初の微分は低次数比較のもとで右制限と左制限の差。
方針：二つの面の形式的余積での計算を評価し、交代和の符号を計算する。
規約：微分の向きに従い右制限から左制限を引く。
使われ方：TT §3・§8、Toën §3.2 の層条件と実際の Čech 複体の接続。
-/
lemma openCech_firstDifferential :
    (openCechZeroIso U P).inv ≫ ((cechComplexFunctor U).obj P).d 0 1 ≫
        (openCechOneIso U P).hom =
      TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes P U -
        TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes P U := by
  let E := (FormalCoproduct.evalOp (Opens X) A).obj P
  have hd : ((cechComplexFunctor U).obj P).d 0 1 =
      E.map ((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ (0 : Fin 2)).op).op -
        E.map ((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ (1 : Fin 2)).op).op := by
    dsimp only [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
      Functor.comp_obj, AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj]
    refine (CochainComplex.of_d _ _ 0).trans ?_
    simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two,
      CosimplicialObject.δ, E, sub_eq_add_neg]
  rw [hd]
  change E.map (openCechZeroFormalIso U).hom.op ≫ (_ - _) ≫
    E.map (openCechOneFormalIso U).inv.op = _
  simp only [comp_sub, sub_comp, ← E.map_comp, ← op_comp, Category.assoc]
  rw [openCech_zeroFace, openCech_oneFace]
  rfl

end SerrePositivity.KST.DerivedGeometry
