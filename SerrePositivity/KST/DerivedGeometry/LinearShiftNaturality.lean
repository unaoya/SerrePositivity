module

public import SerrePositivity.KST.DerivedGeometry.LinearPretriangulation

/-!
概要：代表加群の shift 比較の chain map に関する自然性を証明する。
方針：右 shift の各成分と元の複体の shift の射を直接比較する。
規約：次数の取り替えに伴う同一視も含めて照合する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の三角構造と導来局所化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

/--
概要：右 shift は chain map による後合成と両立する。
方針：cochain の各成分で shift の射の公式を使う。
規約：任意の整数次数の cochain を扱う。
使われ方：Drinfeld §2.4、KST D4 の代表加群の shift 比較の自然性。
-/
theorem rightShift_postcompose {T X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (s q : ℤ) (a : Cochain T X (q + s)) :
    (a.comp (Cochain.ofHom f) (add_zero _)).rightShift s q rfl =
      (a.rightShift s q rfl).comp (Cochain.ofHom (f⟦s⟧')) (add_zero _) := by
  ext p r h
  subst r
  simp [Cochain.rightShift, Cochain.ofHom_v, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq, add_assoc, Category.assoc]

/--
概要：写像複体の右 shift 比較は chain map の後合成に関して自然。
方針：各次数の cochain に既存の右 shift と後合成の公式を適用する。
規約：shift の微分の符号を保つ同じ chain map を使う。
使われ方：Drinfeld §2.4、KST D4 の shift の自然同型。
-/
theorem mappingShiftMap_naturality (T : CochainComplex C ℤ)
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) (s : ℤ) :
    (mappingPostcompose A T f)⟦s⟧' ≫ mappingShiftMap A T Y s =
      mappingShiftMap A T X s ≫ mappingPostcompose A T (f⟦s⟧') := by
  ext q a
  exact rightShift_postcompose f s q a

/--
概要：写像複体の次数の同一視を cochain の成分で計算する。
方針：次数の等式で帰納し、同一視が恒等射となる場合へ戻す。
規約：対象の宇宙や次数を定義上等しいと仮定しない。
使われ方：Drinfeld §2.4、KST D4 の零・加法 shift の整合性。
-/
theorem mappingComplex_cast_v (T X : CochainComplex C ℤ) {m n : ℤ} (h : m = n)
    (a : Cochain T X m) (p r : ℤ) (hpr : p + n = r) :
    ((ModuleCat.Hom.hom (eqToHom (congrArg (fun i => (mappingComplex A T X).X i) h))) a).v p r hpr =
      a.v p (p + m) rfl ≫ eqToHom (congrArg X.X (by omega : p + m = r)) := by
  subst n
  subst r
  simp

/--
概要：写像複体の右 shift 比較は零 shift の標準同型と両立する。
方針：各 cochain の成分を計算し次数の同一視を照合する。
規約：零 shift を定義上の等号で置き換えない。
使われ方：Drinfeld §2.4、KST D4 の shift の整合性。
-/
theorem mappingShiftMap_zero (T X : CochainComplex C ℤ) :
    mappingShiftMap A T X 0 ≫
      mappingPostcompose A T ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app X) =
      (CategoryTheory.shiftFunctorZero (Complex A) ℤ).hom.app (mappingComplex A T X) := by
  ext q a
  simp [mappingShiftMap, mappingPostcompose, Cochain.rightShift,
    shiftFunctorObjXIso, CochainComplex.shiftFunctorZero_hom_app_f,
    HomologicalComplex.XIsoOfEq]
  ext p r h
  subst r
  simp [Cochain.ofHom_v, Cochain.mk_v,
    CochainComplex.shiftFunctorZero_hom_app_f, HomologicalComplex.XIsoOfEq]
  exact (mappingComplex_cast_v A T X (add_zero q) a p (p + q) rfl).symm

/--
概要：写像複体の右 shift 比較は加法 shift の標準同型と両立する。
方針：二回の右 shift と一回の右 shift の cochain 成分を照合する。
規約：shift の加法の向きと順序を固定する。
使われ方：Drinfeld §2.4、KST D4 の shift の整合性。
-/
theorem mappingShiftMap_add (T X : CochainComplex C ℤ) (s t : ℤ) :
    mappingShiftMap A T X (s + t) ≫
      mappingPostcompose A T ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) s t).hom.app X) =
      (CategoryTheory.shiftFunctorAdd (Complex A) s t).hom.app (mappingComplex A T X) ≫
        (mappingShiftMap A T X s)⟦t⟧' ≫ mappingShiftMap A T (X⟦s⟧) t := by
  ext q a
  simp [mappingShiftMap, mappingPostcompose, Cochain.rightShift,
    shiftFunctorObjXIso, CochainComplex.shiftFunctorAdd_hom_app_f,
    HomologicalComplex.XIsoOfEq, Category.assoc]
  ext p r h
  subst r
  simp [Cochain.ofHom_v, Cochain.mk_v,
    CochainComplex.shiftFunctorAdd_hom_app_f, HomologicalComplex.XIsoOfEq]
  have hc := mappingComplex_cast_v A T X (show q + (s + t) = q + t + s by omega)
    a p (p + (q + t + s)) rfl
  change a.v p (p + (q + (s + t))) rfl ≫
      eqToHom (congrArg X.X (show p + (q + (s + t)) = p + q + t + s by omega)) =
    ((ModuleCat.Hom.hom (eqToHom (congrArg (fun i => (mappingComplex A T X).X i)
      (show q + (s + t) = q + t + s by omega)))) a).v p (p + (q + t + s)) rfl ≫
      eqToHom (congrArg X.X (show p + (q + t + s) = p + q + t + s by omega))
  simpa only [Category.assoc, eqToHom_trans] using
    (congrArg (fun z : T.X p ⟶ X.X (p + (q + t + s)) =>
      z ≫ eqToHom (congrArg X.X
        (show p + (q + t + s) = p + q + t + s by omega))) hc).symm

attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：代表加群の shift 同型は元の複体の chain map に関して自然。
方針：全対象で評価し、写像複体の shift の自然性を使う。
規約：既に構成した代表加群の同型を変更しない。
使われ方：Drinfeld §2.4、KST D4 の三角構造の比較。
-/
def complexYonedaShiftIso (s : ℤ) :
    complexYoneda (C := C) A ⋙ CategoryTheory.shiftFunctor _ s ≅
      CategoryTheory.shiftFunctor _ s ⋙ complexYoneda A :=
  NatIso.ofComponents (fun X => representableShiftIso A X s) (by
    intro X Y f
    apply moduleMorphism_ext
    intro T
    simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp,
      moduleShiftFunctor_eq, moduleShiftFunctor_map_eval, representableShiftIso_hom_eval]
    change ((moduleEvaluation A (CochainComplex C ℤ) T).map
      (representablePostcompose A f))⟦s⟧' ≫ mappingShiftMap A T Y s =
      mappingShiftMap A T X s ≫ (moduleEvaluation A (CochainComplex C ℤ) T).map
        (representablePostcompose A (f⟦s⟧'))
    rw [representablePostcompose_eval, representablePostcompose_eval]
    change (mappingPostcompose A T f)⟦s⟧' ≫ mappingShiftMap A T Y s =
      mappingShiftMap A T X s ≫ mappingPostcompose A T (f⟦s⟧')
    exact mappingShiftMap_naturality A T f s)

end SerrePositivity.KST.DerivedGeometry.LinearComplex
