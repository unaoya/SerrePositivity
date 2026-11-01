module

public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestriction

/-!
# Bimodule.DiagonalRestriction

## 概要
4 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w z t

/-! ## DiagonalRestriction（旧 SerrePositivity/DifferentialGraded/Bimodule/DiagonalRestriction.lean） -/

/-! # dg関手のHom写像による対角bimoduleの制限比較

## 概要
dg関手のHom写像による対角bimoduleの制限比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section DiagonalRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite CochainComplex HomComplex HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 同時制限した対角の左作用は、元の対角左作用へFのHom写像を前合成したもの。 -/
lemma diagonalRestriction_leftAt_map (b d d' : D) :
    ((BimoduleCategory.underlying A D D
      ((BimoduleCategory.pairedRestrictionFunctor A E E D D F F).obj
        (BimoduleCategory.of A E E (diagonal A E)))).leftAt b).map d d' =
      F.map d d' ≫ ((diagonal A E).leftAt (F.obj b)).map (F.obj d) (F.obj d') := by
  change ((rightRestriction A E D D F (leftRestriction A E E D F (diagonal A E))).leftAt b).map
    d d' = _
  rw [rightRestriction_leftAt_map]
  change (F.map d d' ≫ (diagonal A E).map (F.obj d) (F.obj d')) ≫
      moduleHomπ A E _ _ (F.obj b) =
    F.map d d' ≫ ((diagonal A E).map (F.obj d) (F.obj d') ≫ moduleHomπ A E _ _ (F.obj b))
  exact Category.assoc _ _ _

/-- 対角の左作用に対しても、Hom写像は全次数で自然。 -/
lemma diagonalRestriction_value_left_naturality (b d d' : D) :
    ((diagonal A D).leftAt b).map d d' ≫
        homPostcompose ((diagonal A D).value b d) (F.map b d') =
      ((BimoduleCategory.underlying A D D
        ((BimoduleCategory.pairedRestrictionFunctor A E E D D F F).obj
          (BimoduleCategory.of A E E (diagonal A E)))).leftAt b).map d d' ≫
        homPrecompose (F.map b d) ((diagonal A E).value (F.obj b) (F.obj d')) := by
  rw [diagonalRestriction_leftAt_map]
  apply hom_naturality_of_apply
  intro p f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]
  change (F.map b d').f n
      ((((moduleHomπ A D (representable A d) (representable A d') b).f p
        ((yonedaHom A D d d').f p f)).v r n hn) g) =
    (((moduleHomπ A E (representable A (F.obj d)) (representable A (F.obj d')) (F.obj b)).f p
      ((yonedaHom A E (F.obj d) (F.obj d')).f p ((F.map d d').f p f))).v r n hn)
        ((F.map b d).f r g)
  rw [yonedaHom_element, yonedaHom_element]
  simpa only [Units.smul_def, map_zsmul] using
    congrArg (fun h => (p * r).negOnePow • h) (F.map_forward A g f hn)

/-- 各右加群上の既存representableRestrictionMapを対角bimodule射に束ねる。 -/
def diagonalRestrictionMap :
    BimoduleCategory.of A D D (diagonal A D) ⟶
      (BimoduleCategory.pairedRestrictionFunctor A E E D D F F).obj
        (BimoduleCategory.of A E E (diagonal A E)) :=
  ⟨fun d => representableRestrictionMap A D E F d, by
    intro d d'
    apply moduleHom_ext
    intro b
    simp only [Category.assoc]
    rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
    simp only [moduleMorphismComponent]
    rw [representableRestrictionMap_eval, representableRestrictionMap_eval]
    have h := diagonalRestriction_value_left_naturality A D E F b d d'
    change ((diagonal A D).map d d' ≫ moduleHomπ A D _ _ b) ≫ _ =
      ((BimoduleCategory.underlying A D D
        ((BimoduleCategory.pairedRestrictionFunctor A E E D D F F).obj
          (BimoduleCategory.of A E E (diagonal A E)))).map d d' ≫
            moduleHomπ A D _ _ b) ≫ _ at h
    exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))⟩

@[simp]
lemma diagonalRestrictionMap_value (b d : D) :
    (BimoduleCategory.valueEvaluation A D D b d).map (diagonalRestrictionMap A D E F) =
      F.map b d :=
  representableRestrictionMap_eval A D E F d b

lemma diagonalRestrictionMap_quasiIso_iff :
    BimoduleCategory.quasiIso A D D (diagonalRestrictionMap A D E F) ↔ HomQuasiIso F := by
  constructor
  · intro h b d
    rw [← diagonalRestrictionMap_value A D E F b d]
    exact h b d
  · intro h b d
    rw [diagonalRestrictionMap_value]
    exact h b d

end SerrePositivity.DifferentialGraded.Bimodule
end

end DiagonalRestriction

/-! ## DiagonalRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Bimodule/DiagonalRestrictionCoherence.lean） -/

/-! # Hom写像による対角制限比較の恒等・合成則

## 概要
Hom写像による対角制限比較の恒等・合成則。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section DiagonalRestrictionCoherence

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 恒等関手の対角比較は既存の恒等制限比較の逆射。 -/
lemma diagonalRestrictionMap_id :
    diagonalRestrictionMap A D D (DGFunctor.id D) ≫
        (BimoduleCategory.pairedRestrictionIdObjIso A D D
          (BimoduleCategory.of A D D (diagonal A D))).hom = 𝟙 _ := by
  apply BimoduleCategory.value_hom_ext A D D
  intro b d
  rw [CategoryTheory.Functor.map_comp, diagonalRestrictionMap_value,
    BimoduleCategory.pairedRestrictionIdObjIso_hom_value, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階のHom写像による対角比較は、合成dg関手の比較そのもの。 -/
lemma diagonalRestrictionMap_comp :
    diagonalRestrictionMap A D E F ≫
        (BimoduleCategory.pairedRestrictionFunctor A E E D D F F).map
          (diagonalRestrictionMap A E T G) ≫
        (BimoduleCategory.pairedRestrictionCompObjIso A T T E E D D F G F G
          (BimoduleCategory.of A T T (diagonal A T))).hom =
      diagonalRestrictionMap A D T (F.comp G) := by
  apply BimoduleCategory.value_hom_ext A D D
  intro b d
  simp only [CategoryTheory.Functor.map_comp, diagonalRestrictionMap_value,
    BimoduleCategory.pairedRestrictionFunctor_map_value,
    BimoduleCategory.pairedRestrictionCompObjIso_hom_value, Category.comp_id]
  rfl

end SerrePositivity.DifferentialGraded.Bimodule
end

end DiagonalRestrictionCoherence

/-! ## PairedRestrictionPresentation（旧 SerrePositivity/DifferentialGraded/Bimodule/PairedRestrictionPresentation.lean） -/

/-! # 直接両端制限と積dg圏上の既存制限の表示比較

## 概要
直接両端制限と積dg圏上の既存制限の表示比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PairedRestrictionPresentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D B) (G : DGFunctor A E C)

/-- 直接両端制限と積dg関手制限の、値で恒等となる全Hom自然な表示比較。 -/
def pairedRestrictionPresentationObjIso (P : BimoduleCategory A B C) :
    (rightModuleFunctor A D E).obj
        ((BimoduleCategory.pairedRestrictionFunctor A B C D E F G).obj P) ≅
      (moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (bimoduleRestrictionIndex A D E B C F G)).obj ((rightModuleFunctor A B C).obj P) :=
  moduleIsoMk A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    refine (CochainComplex.HomComplex.Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (CochainComplex.HomComplex.Cochain.id_comp _).symm
    change ((𝟙 _ ≫
      (Bimodule.rightRestriction A B D E F
        (Bimodule.leftRestriction A B C E G (BimoduleCategory.underlying A B C P))).uncurryHom
          x.unop.unop y.unop.unop).f p f) =
      (((F.op.map x.unop.unop.1 y.unop.unop.1 ⊗ₘ G.map x.unop.unop.2 y.unop.unop.2) ≫
        (𝟙 _ ≫ (BimoduleCategory.underlying A B C P).uncurryHom
          (F.op.obj x.unop.unop.1, G.obj x.unop.unop.2)
          (F.op.obj y.unop.unop.1, G.obj y.unop.unop.2))).f p f)
    simp only [Category.id_comp]
    exact congrArg (fun k => k.f p f) (Bimodule.pairedRestriction_uncurryHom A B C D E F G
      (BimoduleCategory.underlying A B C P) x.unop.unop y.unop.unop))

@[simp]
lemma pairedRestrictionPresentationObjIso_hom_eval (P : BimoduleCategory A B C)
    (x : (DGTensorCategory A Dᵒᵖ E)ᵒᵖ) :
    (moduleEvaluation A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ x).map
        (pairedRestrictionPresentationObjIso A B C D E F G P).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ _ _ x

/-- 両端制限の表示squareは任意の閉零bimodule射に自然。 -/
def pairedRestrictionPresentationIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ⋙ rightModuleFunctor A D E ≅
      rightModuleFunctor A B C ⋙
        moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
          (bimoduleRestrictionIndex A D E B C F G) :=
  NatIso.ofComponents (pairedRestrictionPresentationObjIso A B C D E F G) (by
    intro P Q q
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, pairedRestrictionPresentationObjIso_hom_eval,
      Functor.comp_map]
    have h := rightModuleFunctor_map_value A D E
      ((BimoduleCategory.pairedRestrictionFunctor A B C D E F G).map q)
      x.unop.1.unop x.unop.2
    have h' := moduleRestriction_map_eval A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
      (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (bimoduleRestrictionIndex A D E B C F G)
      ((rightModuleFunctor A B C).map q) x
    exact h.trans ((BimoduleCategory.pairedRestrictionFunctor_map_value A B C D E F G q
      x.unop.1.unop x.unop.2).trans
        ((rightModuleFunctor_map_value A B C q (F.obj x.unop.1.unop)
          (G.obj x.unop.2)).symm.trans h'.symm)))

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
end

end PairedRestrictionPresentation

/-! ## MiddleRestrictionPresentation（旧 SerrePositivity/DifferentialGraded/Bimodule/MiddleRestrictionPresentation.lean） -/

/-! # 左右の中間制限と積dg圏上の明示的右加群表示の比較

## 概要
左右の中間制限と積dg圏上の明示的右加群表示の比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRestrictionPresentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)

/-- 左制限の両表示は値で恒等の全Hom自然な右加群同型で結ばれる。 -/
def middleLeftPresentationObjIso (P : BimoduleCategory A B C) :
    (rightModuleFunctor A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P) ≅
      (moduleRestriction A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ
        (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ((DGFunctor.id Bᵒᵖ).tensor F).op.op).obj
        ((rightModuleFunctor A B C).obj P) :=
  moduleIsoMk A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    refine (CochainComplex.HomComplex.Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (CochainComplex.HomComplex.Cochain.id_comp _).symm
    change ((𝟙 _ ≫
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)).uncurryHom
        x.unop.unop y.unop.unop).f p f) =
      (((𝟙 _ ⊗ₘ F.map x.unop.unop.2 y.unop.unop.2) ≫
        (𝟙 _ ≫ (BimoduleCategory.underlying A B C P).uncurryHom
          (x.unop.unop.1, F.obj x.unop.unop.2)
          (y.unop.unop.1, F.obj y.unop.unop.2))).f p f)
    simp only [Category.id_comp]
    exact congrArg (fun k => k.f p f)
      (Bimodule.leftRestriction_uncurryHom A B C D F
        (BimoduleCategory.underlying A B C P) x.unop.unop y.unop.unop))

@[simp]
lemma middleLeftPresentationObjIso_hom_eval (P : BimoduleCategory A B C)
    (x : (DGTensorCategory A Bᵒᵖ D)ᵒᵖ) :
    (moduleEvaluation A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ x).map
      (middleLeftPresentationObjIso A B C D F P).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ _ _ x

/-- 明示的表示の左制限squareは任意の閉零bimodule射について自然。 -/
def middleLeftPresentationIso :
    BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ rightModuleFunctor A B D ≅
      rightModuleFunctor A B C ⋙
        moduleRestriction A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
          ((DGFunctor.id Bᵒᵖ).tensor F).op.op :=
  NatIso.ofComponents (middleLeftPresentationObjIso A B C D F) (by
    intro P P' f
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, middleLeftPresentationObjIso_hom_eval,
      Functor.comp_map]
    have h := rightModuleFunctor_map_value A B D
      ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map f)
      x.unop.1.unop x.unop.2
    have h' := moduleRestriction_map_eval A (DGTensorCategory A Bᵒᵖ D)ᵒᵖ
      (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ((DGFunctor.id Bᵒᵖ).tensor F).op.op
      ((rightModuleFunctor A B C).map f) x
    exact h.trans ((BimoduleCategory.middleLeftRestrictionMap_value_eval A B C D F f
      x.unop.1.unop x.unop.2).trans
        ((rightModuleFunctor_map_value A B C f x.unop.1.unop (F.obj x.unop.2)).symm.trans
          h'.symm)))

variable (E : Type t) [DGCategory A E] [Small.{u} E]

/-- 右制限の両表示も各値で恒等となる全Hom自然な右加群同型。 -/
def middleRightPresentationObjIso (Q : BimoduleCategory A C E) :
    (rightModuleFunctor A D E).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q) ≅
      (moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
        (DGTensorCategory A Cᵒᵖ E)ᵒᵖ (F.op.tensor (DGFunctor.id E)).op.op).obj
        ((rightModuleFunctor A C E).obj Q) :=
  moduleIsoMk A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    refine (CochainComplex.HomComplex.Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (CochainComplex.HomComplex.Cochain.id_comp _).symm
    change ((𝟙 _ ≫
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q)).uncurryHom
        x.unop.unop y.unop.unop).f p f) =
      (((F.op.map x.unop.unop.1 y.unop.unop.1 ⊗ₘ 𝟙 _) ≫
        (𝟙 _ ≫ (BimoduleCategory.underlying A C E Q).uncurryHom
          (F.op.obj x.unop.unop.1, x.unop.unop.2)
          (F.op.obj y.unop.unop.1, y.unop.unop.2))).f p f)
    simp only [Category.id_comp]
    exact congrArg (fun k => k.f p f)
      (Bimodule.rightRestriction_uncurryHom A C D E F
        (BimoduleCategory.underlying A C E Q) x.unop.unop y.unop.unop))

@[simp]
lemma middleRightPresentationObjIso_hom_eval (Q : BimoduleCategory A C E)
    (x : (DGTensorCategory A Dᵒᵖ E)ᵒᵖ) :
    (moduleEvaluation A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ x).map
      (middleRightPresentationObjIso A C D F E Q).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ _ _ x

/-- 明示的表示の右制限squareは任意の閉零bimodule射について自然。 -/
def middleRightPresentationIso :
    BimoduleCategory.middleRightRestrictionFunctor A C D E F ⋙ rightModuleFunctor A D E ≅
      rightModuleFunctor A C E ⋙
        moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Cᵒᵖ E)ᵒᵖ
          (F.op.tensor (DGFunctor.id E)).op.op :=
  NatIso.ofComponents (middleRightPresentationObjIso A C D F E) (by
    intro Q Q' f
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, middleRightPresentationObjIso_hom_eval,
      Functor.comp_map]
    have h := rightModuleFunctor_map_value A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).map f)
      x.unop.1.unop x.unop.2
    have h' := moduleRestriction_map_eval A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
      (DGTensorCategory A Cᵒᵖ E)ᵒᵖ (F.op.tensor (DGFunctor.id E)).op.op
      ((rightModuleFunctor A C E).map f) x
    exact h.trans ((BimoduleCategory.middleRightRestrictionMap_value_eval A C D E F f
      x.unop.1.unop x.unop.2).trans
        ((rightModuleFunctor_map_value A C E f (F.obj x.unop.1.unop) x.unop.2).symm.trans
          h'.symm)))

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
end

end MiddleRestrictionPresentation
