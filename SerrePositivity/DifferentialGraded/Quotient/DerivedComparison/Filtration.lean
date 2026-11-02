module

public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import SerrePositivity.DifferentialGraded.Quotient.Composition
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.LinearAlgebra.Span.Defs
public import SerrePositivity.DifferentialGraded.Complexes.ExactColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Quotient.DerivedComparison.Filtration

## 概要
商関手の延長と path 長 filtration・次数層・作用をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Extension（旧 SerrePositivity/DifferentialGraded/Quotient/Extension.lean） -/

/-! # 指定収縮付きdg関手の商への延長と制限との一方の往復 -/

@[expose] public section Extension
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 各εを指定収縮へ送る、主豊穣モデル上の実際のdg関手。 -/
def extension (C : ContractedFunctor A D S E) : DGFunctor A (QuotientObject D S) E where
  obj x := C.toDGFunctor.obj x.val
  map x y := quotientEvaluation A C x.val y.val
  map_id x := quotientEvaluation_unit A C x.val
  map_comp x y z := quotientEvaluation_composition A C x.val y.val z.val

lemma inclusion_comp_extension (C : ContractedFunctor A D S E) :
    (inclusion A D S).comp (extension A C) = C.toDGFunctor := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (inclusion A D S).comp (extension A C)) (G := C.toDGFunctor) (fun _ => rfl)
  intro x y
  change (originalHomInclusion A D S x y ≫ quotientEvaluation A C x y) ≫ eqToHom (by rfl) = _
  rw [eqToHom_refl, Category.comp_id, quotientEvaluation_original]

lemma restrict_extension_homotopy (C : ContractedFunctor A D S E) (b : S) :
    (restrictContractedFunctor A D S (extension A C)).homotopy b = C.homotopy b :=
  quotientEvaluation_epsilon A C b

omit [Small.{u} D] in
lemma ContractedFunctor.ext {C C' : ContractedFunctor A D S E}
    (hf : C.toDGFunctor = C'.toDGFunctor) (hh : HEq C.homotopy C'.homotopy) : C = C' := by
  cases C
  cases C'
  cases hf
  cases hh
  rfl

lemma restrict_extension (C : ContractedFunctor A D S E) :
    restrictContractedFunctor A D S (extension A C) = C := by
  apply ContractedFunctor.ext A
  · exact inclusion_comp_extension A C
  · exact heq_of_eq (funext (fun b => restrict_extension_homotopy A C b))

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Extension

/-! ## Reconstruction（旧 SerrePositivity/DifferentialGraded/Quotient/Reconstruction.lean） -/

/-! # 商dg関手を制限データのpath評価から再構成する -/

@[expose] public section Reconstruction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 商dg関手のHom写像を内部微分の始域上の次数0 cochainとして読む。 -/
def restrictionHomCochain (G : DGFunctor A (QuotientObject D S) E) (x y : D) :
    Cochain (internalHom A D S x y) (homObject A E (G.obj ⟨x⟩) (G.obj ⟨y⟩)) 0 :=
  Cochain.ofHoms (fun i => (G.map ⟨x⟩ ⟨y⟩).f i)

lemma restrictionHomCochain_path (G : DGFunctor A (QuotientObject D S) E)
    (w : Word S) (x y : D) :
    (Cochain.ofHom (ι A D S x y w)).comp (restrictionHomCochain A G x y) (zero_add 0) =
      pathEvaluation A (restrictContractedFunctor A D S G) w x y := by
  induction w generalizing x with
  | nil =>
    apply Cochain.ext₀
    intro i
    simp only [pathEvaluation_nil, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      restrictionHomCochain, Cochain.ofHoms_v]
    rfl
  | cons b w ih =>
    apply epsilonMiddleCochain_ext₀ A
    intro p q n hn a t
    have h := congrArg (fun v : (quotientHom A D S x y).X n => (G.map ⟨x⟩ ⟨y⟩).f n v)
      (path_inclusion_generator A D b w x y p q n hn a t)
    rw [DGFunctor.map_forward A G (x := ⟨x⟩) (y := ⟨b.val⟩) (z := ⟨y⟩),
      DGFunctor.map_forward A G (x := ⟨b.val⟩) (y := ⟨b.val⟩) (z := ⟨y⟩)] at h
    have ht := congrArg (fun f : Cochain (term A D w b.val y)
        (homObject A E (G.obj ⟨b.val⟩) (G.obj ⟨y⟩)) 0 =>
      f.v q q (add_zero q) t) (ih b.val)
    rw [cochain_ofHom_comp_apply, restrictionHomCochain, Cochain.ofHoms_v] at ht
    have htail := congrArg (fun z : (homObject A E (G.obj ⟨b.val⟩) (G.obj ⟨y⟩)).X q =>
      forward A
        ((G.map ⟨x⟩ ⟨b.val⟩).f p ((originalHomInclusion A D S x b.val).f p a))
        (forward A ((G.map ⟨b.val⟩ ⟨b.val⟩).f (-1) (epsilonElement A D S b)) z rfl)
        hn) ht
    let v : (term A D (b :: w) x y).X n :=
      ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        p ((-1) + q) n hn (a ⊗ₜ[A]
          ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
            ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))
    have he := cochain_ofHom_comp_apply (ι A D S x y (b :: w))
      (restrictionHomCochain A G x y) (add_zero n) v
    rw [restrictionHomCochain, Cochain.ofHoms_v] at he
    have hr := pathEvaluation_cons_generator A (restrictContractedFunctor A D S G)
      b w x y p q n hn a t
    exact he.trans (h.trans (htail.trans hr.symm))

lemma restrictionHomCochain_eq_internalEvaluation (G : DGFunctor A (QuotientObject D S) E)
    (x y : D) :
    restrictionHomCochain A G x y =
      internalEvaluation A (restrictContractedFunctor A D S G) x y := by
  apply pathCochain_ext A D S x y 0
  intro w
  rw [restrictionHomCochain_path, internalEvaluation_precomp]

lemma extension_restrict (G : DGFunctor A (QuotientObject D S) E) :
    extension A (restrictContractedFunctor A D S G) = G := by
  apply EnrichedFunctor.ext (Complex A)
    (F := extension A (restrictContractedFunctor A D S G)) (G := G) (fun _ => rfl)
  intro x y
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      change quotientEvaluation A (restrictContractedFunctor A D S G) x y ≫
        eqToHom (by rfl) = G.map ⟨x⟩ ⟨y⟩
      rw [eqToHom_refl, Category.comp_id]
      apply HomologicalComplex.Hom.ext
      funext i
      rw [quotientEvaluation_f]
      have h := congrArg (fun f : Cochain (internalHom A D S x y)
          (homObject A E (G.obj ⟨x⟩) (G.obj ⟨y⟩)) 0 =>
        f.v i i (add_zero i)) (restrictionHomCochain_eq_internalEvaluation A G x y).symm
      simpa only [restrictionHomCochain, Cochain.ofHoms_v] using h

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Reconstruction

/-! ## Universal（旧 SerrePositivity/DifferentialGraded/Quotient/Universal.lean） -/

/-! # 指定収縮データ付きdg関手に関する明示的商の厳密普遍性 -/

@[expose] public section Universal
universe u v w t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商からのdg関手は、元のdg関手と選択済み収縮データと一対一に対応する。 -/
def universalEquiv (S : Set D) (E : Type w) [DGCategory A E] :
    DGFunctor A (QuotientObject D S) E ≃ ContractedFunctor A D S E where
  toFun := restrictContractedFunctor A D S
  invFun := extension A
  left_inv := extension_restrict A
  right_inv := restrict_extension A

variable {D} {S : Set D} {E : Type w} [DGCategory A E]

lemma extension_unique (G : DGFunctor A (QuotientObject D S) E)
    (C : ContractedFunctor A D S E) (h : restrictContractedFunctor A D S G = C) :
    G = extension A C := by
  rw [← h, extension_restrict]

lemma existsUnique_extension (C : ContractedFunctor A D S E) :
    ∃! G : DGFunctor A (QuotientObject D S) E, restrictContractedFunctor A D S G = C := by
  refine ⟨extension A C, restrict_extension A C, ?_⟩
  intro G hG
  exact extension_unique A G C hG

variable {T : Type t} [DGCategory A T]

lemma restrictContractedFunctor_comp (G : DGFunctor A (QuotientObject D S) E)
    (H : DGFunctor A E T) :
    restrictContractedFunctor A D S (G.comp H) =
      (restrictContractedFunctor A D S G).postcomp A H := by
  apply ContractedFunctor.ext A
  · apply EnrichedFunctor.ext (Complex A)
      (F := (restrictContractedFunctor A D S (G.comp H)).toDGFunctor)
      (G := ((restrictContractedFunctor A D S G).postcomp A H).toDGFunctor) (fun _ => rfl)
    intro x y
    change (originalHomInclusion A D S x y ≫ (G.map ⟨x⟩ ⟨y⟩ ≫
        H.map (G.obj ⟨x⟩) (G.obj ⟨y⟩))) ≫ eqToHom (by rfl) =
      (originalHomInclusion A D S x y ≫ G.map ⟨x⟩ ⟨y⟩) ≫ H.map (G.obj ⟨x⟩) (G.obj ⟨y⟩)
    rw [eqToHom_refl, Category.comp_id, Category.assoc]
  · exact heq_of_eq (funext (fun _ => rfl))

lemma extension_postcomp (C : ContractedFunctor A D S E) (H : DGFunctor A E T) :
    extension A (C.postcomp A H) = (extension A C).comp H := by
  apply (universalEquiv A D S T).injective
  change restrictContractedFunctor A D S (extension A (C.postcomp A H)) =
    restrictContractedFunctor A D S ((extension A C).comp H)
  rw [restrict_extension, restrictContractedFunctor_comp, restrict_extension]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end Universal

/-! ## ParameterExtension（旧 SerrePositivity/DifferentialGraded/Quotient/ParameterExtension.lean） -/

/-!
概要：選択された収縮と整合する全パラメータ変換を、同じ実商へ厳密に延長する。
方針：元 Hom の自然性と指定 ε の自然性から、全 path の全次数自然性を導く。
規約：収縮との整合はここでは明示する。D-8 e の実選択での充足は別途構成する。
使われ方：模型を変えず、同じ四角形の商辺・零角辺を全 native Hom 上で動かす部品。
-/

@[expose] public section ParameterExtension
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory R E]
  (C C' : ContractedFunctor R D S E) {K : Complex R}
  (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) C.toDGFunctor C'.toDGFunctor)

def parameterExtension
    (hε : ∀ (b : S) (k : ℤ) (t : K.X k),
      forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
        (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega)) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K) (extension R C) (extension R C') where
  app x := τ.app x.val
  naturality x y := by
    apply (gradedFamilyNaturality_iff_homogeneous R (extension R C) (extension R C')
      (fun z => τ.app z.val) x y).2
    intro k p t f
    apply homogeneousNaturality_of_generators R D S (extension R C) (extension R C')
      (fun z => (τ.app z.val).f k t) _ _ x y p f
    · intro a b q g
      have h := (gradedFamilyNaturality_iff_homogeneous R C.toDGFunctor C'.toDGFunctor
        τ.app a b).1 (τ.naturality a b) k q t g
      have hc := congrArg (fun m => m.f q g) (quotientEvaluation_original R C a b)
      have hc' := congrArg (fun m => m.f q g) (quotientEvaluation_original R C' a b)
      change (quotientEvaluation R C a b).f q ((originalHomInclusion R D S a b).f q g) =
        (C.toDGFunctor.map a b).f q g at hc
      change (quotientEvaluation R C' a b).f q ((originalHomInclusion R D S a b).f q g) =
        (C'.toDGFunctor.map a b).f q g at hc'
      change forward R ((quotientEvaluation R C a b).f q
        ((originalHomInclusion R D S a b).f q g)) ((τ.app b).f k t) rfl =
          (k * q).negOnePow • forward R ((τ.app a).f k t)
            ((quotientEvaluation R C' a b).f q
              ((originalHomInclusion R D S a b).f q g)) (by omega)
      rw [hc, hc']
      exact h
    · intro b
      change forward R ((quotientEvaluation R C b.val b.val).f (-1)
        (epsilonElement R D S b)) ((τ.app b.val).f k t) rfl =
          (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t)
            ((quotientEvaluation R C' b.val b.val).f (-1) (epsilonElement R D S b)) (by omega)
      rw [quotientEvaluation_epsilon, quotientEvaluation_epsilon]
      exact hε b k t

lemma parameterExtension_app
    (hε : ∀ (b : S) (k : ℤ) (t : K.X k),
      forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
        (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega))
    (x : D) : (parameterExtension R C C' τ hε).app ⟨x⟩ = τ.app x := rfl

lemma parameterExtension_epsilon_necessary
    (σ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) (extension R C) (extension R C'))
    (hσ : ∀ x : D, σ.app ⟨x⟩ = τ.app x)
    (b : S) (k : ℤ) (t : K.X k) :
    forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
      (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega) := by
  have h := (gradedFamilyNaturality_iff_homogeneous R (extension R C) (extension R C')
    σ.app ⟨b.val⟩ ⟨b.val⟩).1 (σ.naturality ⟨b.val⟩ ⟨b.val⟩)
      k (-1) t (epsilonElement R D S b)
  change forward R ((quotientEvaluation R C b.val b.val).f (-1) (epsilonElement R D S b))
    ((σ.app ⟨b.val⟩).f k t) rfl =
      (k * (-1)).negOnePow • forward R ((σ.app ⟨b.val⟩).f k t)
        ((quotientEvaluation R C' b.val b.val).f (-1) (epsilonElement R D S b)) (by omega) at h
  rw [hσ b.val, quotientEvaluation_epsilon, quotientEvaluation_epsilon] at h
  exact h

/-- 同じ成分を保持する商上の全パラメータ延長の、正確な必要十分条件。 -/
theorem parameterExtension_exists_iff :
    (∃ σ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
        (extension R C) (extension R C'), ∀ x : D, σ.app ⟨x⟩ = τ.app x) ↔
      ∀ (b : S) (k : ℤ) (t : K.X k),
        forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
          (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact parameterExtension_epsilon_necessary R C C' τ σ hσ
  · intro hε
    exact ⟨parameterExtension R C C' τ hε, fun _ => rfl⟩

theorem parameterExtension_unique
    (σ σ' : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) (extension R C) (extension R C'))
    (h : ∀ x : D, σ.app ⟨x⟩ = σ'.app ⟨x⟩) : σ = σ' := by
  apply GradedNatTrans.ext
  funext x
  rcases x with ⟨x⟩
  exact h x

/-- 任意のパラメータ射で制限しても、同じ延長を厳密に回収する。 -/
theorem parameterExtension_reindex
    (hε : ∀ (b : S) (k : ℤ) (t : K.X k),
      forward R (C.homotopy b) ((τ.app b.val).f k t) rfl =
        (k * (-1)).negOnePow • forward R ((τ.app b.val).f k t) (C'.homotopy b) (by omega))
    {L : Complex R} (f : L ⟶ K) :
    parameterExtension R C C'
        ((enrichedNatTransYoneda C.toDGFunctor C'.toDGFunctor).map f.op τ)
        (fun b k t => hε b k (f.f k t)) =
      (enrichedNatTransYoneda (extension R C) (extension R C')).map f.op
        (parameterExtension R C C' τ hε) := by
  apply parameterExtension_unique R C C'
  intro x
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ParameterExtension

/-! ## ParameterPostcomposition（旧 SerrePositivity/DifferentialGraded/Quotient/ParameterPostcomposition.lean） -/

/-!
概要：同じ選択収縮の後合成族について、全パラメータの商延長を実構成する。
方針：後合成側の元の全次数自然性を選択収縮そのものに適用する。
規約：この経路の ε 整合を追加入力に残さず、選んだ収縮を変更しない。
使われ方：D-8 e の同じ実商・零角辺の全 native Hom 作用の後合成部品。
-/

@[expose] public section ParameterPostcomposition
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {E : Type w} [DGCategory R E] {T : Type z} [DGCategory R T]

/-- 元の dg 関手による全パラメータ変換の厳密な前合成。 -/
def parameterPrecomposition (F : DGFunctor R D E) {K : Complex R}
    {H H' : DGFunctor R E T}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) H H') :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K) (F.comp H) (F.comp H') where
  app x := τ.app (F.obj x)
  naturality x y := by
    apply (gradedFamilyNaturality_iff_homogeneous R (F.comp H) (F.comp H')
      (fun x => τ.app (F.obj x)) x y).2
    intro k p t f
    exact (gradedFamilyNaturality_iff_homogeneous R H H' τ.app (F.obj x) (F.obj y)).1
      (τ.naturality (F.obj x) (F.obj y)) k p t ((F.map x y).f p f)

private lemma parameterTrans_hext {K : Complex R} {F F' G G' : DGFunctor R D T}
    (hF : F = F') (hG : G = G')
    (a : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) F G)
    (b : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) F' G')
    (h : HEq a.app b.app) : HEq a b := by
  cases hF
  cases hG
  apply heq_of_eq
  exact GradedNatTrans.ext (eq_of_heq h)

variable [Small.{u} D] {S : Set D} (C : ContractedFunctor R D S E)
  {K : Complex R} {H H' : DGFunctor R E T}
  (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K) H H')

/-- 同じ選択収縮への自然性から ε 整合を実証した全パラメータ延長。 -/
def parameterExtension_postcomposition :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
      (extension R (C.postcomp R H)) (extension R (C.postcomp R H')) :=
  parameterExtension R (C.postcomp R H) (C.postcomp R H')
    (parameterPrecomposition R C.toDGFunctor τ) (fun b k t =>
      (gradedFamilyNaturality_iff_homogeneous R H H' τ.app
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)).1
          (τ.naturality _ _) k (-1) t (C.homotopy b))

lemma parameterExtension_postcomposition_app (x : QuotientObject D S) :
    (parameterExtension_postcomposition R C τ).app x = τ.app (C.toDGFunctor.obj x.val) := rfl

/-- 元の厳密な商延長の後合成等号のもとで、全パラメータ変換も同じ前合成作用。 -/
theorem parameterExtension_postcomposition_heq :
    HEq (parameterExtension_postcomposition R C τ)
      (parameterPrecomposition R (extension R C) τ) := by
  exact parameterTrans_hext R (extension_postcomp R C H) (extension_postcomp R C H')
    (parameterExtension_postcomposition R C τ) (parameterPrecomposition R (extension R C) τ) HEq.rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end ParameterPostcomposition

/-! ## DerivedComparisonFiltration（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFiltration.lean） -/

/-! # 最終 dg 商 Hom の path 長 filtration

長さ n 以下の全 path の次数ごとの像の和を用いる。
内部微分は長さを保ち、ε 消去は長さを下げるので、最終微分でも部分複体をなす。
-/

@[expose] public section DerivedComparisonFiltration
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 長さ n 以下の path が生成する各次数の部分加群。 -/
def lengthSubmodule (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    Submodule A ((internalHom A D S x y).X i) :=
  ⨆ (w : Word S) (_ : w.length ≤ n), LinearMap.range ((ι A D S x y w).f i).hom

lemma path_mem_lengthSubmodule (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (w : Word S) (hw : w.length ≤ n) (z : (term A D w x y).X i) :
    (ι A D S x y w).f i z ∈ lengthSubmodule A D S x y n i := by
  have h : LinearMap.range ((ι A D S x y w).f i).hom ≤ lengthSubmodule A D S x y n i :=
    le_iSup_of_le w (le_iSup_of_le hw le_rfl)
  exact h ⟨z, rfl⟩

lemma lengthSubmodule_mono (S : Set D) (x y : D) {m n : ℕ} (hmn : m ≤ n) (i : ℤ) :
    lengthSubmodule A D S x y m i ≤ lengthSubmodule A D S x y n i := by
  refine iSup_le (fun w => iSup_le (fun hw => ?_))
  rintro z ⟨t, rfl⟩
  exact path_mem_lengthSubmodule A D S x y n i w (hw.trans hmn) t

/-- 全消去作用素の各 path 上の成分は、実際の短い path の有限和である。 -/
lemma erasure_path_apply (S : Set D) (x y : D) (w : Word S) (i : ℤ)
    (z : (term A D w x y).X i) :
    (erasure A D S x y).v i (i + 1) rfl ((ι A D S x y w).f i z) =
      ∑ j ∈ Finset.range w.length,
        (ι A D S x y (w.eraseIdx j)).f (i + 1) ((eraseFace A D w j x y).v i (i + 1) rfl z) := by
  let ev : Cochain (term A D w x y) (internalHom A D S x y) 1 →+
      (internalHom A D S x y).X (i + 1) :=
    { toFun := fun f => f.v i (i + 1) rfl z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h := congrArg ev (erasure_precomp A D S x y w)
  rw [eraseRow, map_sum] at h
  simpa only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    eraseSummand, Cochain.comp_zero_cochain_v, ModuleCat.comp_apply] using h

lemma erasure_path_mem_lengthSubmodule (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (w : Word S) (hw : w.length ≤ n) (z : (term A D w x y).X i) :
    (erasure A D S x y).v i (i + 1) rfl ((ι A D S x y w).f i z) ∈
      lengthSubmodule A D S x y n (i + 1) := by
  rw [erasure_path_apply]
  apply Submodule.sum_mem
  intro j hj
  exact path_mem_lengthSubmodule A D S x y n (i + 1) (w.eraseIdx j)
    ((List.length_eraseIdx_le w j).trans hw) _

/-- 最終微分は長さの切断を保つ。 -/
lemma lengthSubmodule_d (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    lengthSubmodule A D S x y n i ≤
      (lengthSubmodule A D S x y n (i + 1)).comap ((quotientHom A D S x y).d i (i + 1)).hom := by
  refine iSup_le (fun w => iSup_le (fun hw => ?_))
  rintro z ⟨t, rfl⟩
  change (quotientHom A D S x y).d i (i + 1) ((ι A D S x y w).f i t) ∈
    lengthSubmodule A D S x y n (i + 1)
  rw [quotientHom_d]
  change (internalHom A D S x y).d i (i + 1) ((ι A D S x y w).f i t) +
    (erasure A D S x y).v i (i + 1) rfl ((ι A D S x y w).f i t) ∈
      lengthSubmodule A D S x y n (i + 1)
  apply Submodule.add_mem
  · have hc := congrArg (fun f => f t) ((ι A D S x y w).comm i (i + 1))
    simp only [ModuleCat.comp_apply] at hc
    rw [hc]
    exact path_mem_lengthSubmodule A D S x y n (i + 1) w hw _
  · exact erasure_path_mem_lengthSubmodule A D S x y n i w hw t

/-- 最終微分を長さ n 以下の部分加群へ制限した線形写像。 -/
def lengthDifferential (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    lengthSubmodule A D S x y n i →ₗ[A] lengthSubmodule A D S x y n (i + 1) :=
  LinearMap.codRestrict _
    (((quotientHom A D S x y).d i (i + 1)).hom.comp (lengthSubmodule A D S x y n i).subtype)
    (fun z => lengthSubmodule_d A D S x y n i z.property)

lemma lengthDifferential_coe (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : lengthSubmodule A D S x y n i) :
    (lengthDifferential A D S x y n i z).val =
      (quotientHom A D S x y).d i (i + 1) z.val := rfl

/-- dg 商の最終 Hom の長さ n 以下の部分複体。 -/
def lengthComplex (S : Set D) (x y : D) (n : ℕ) : Complex A :=
  CochainComplex.of (fun i => ModuleCat.of A (lengthSubmodule A D S x y n i))
    (fun i => ModuleCat.ofHom (lengthDifferential A D S x y n i)) (fun i => by
      ext z
      exact congrArg (fun f : (quotientHom A D S x y).X i ⟶
        (quotientHom A D S x y).X (i + 1 + 1) => f z.val)
        ((quotientHom A D S x y).d_comp_d i (i + 1) (i + 1 + 1)))

@[simp] lemma lengthComplex_d (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    (lengthComplex A D S x y n).d i (i + 1) =
      ModuleCat.ofHom (lengthDifferential A D S x y n i) :=
  CochainComplex.of_d (fun j => ModuleCat.of A (lengthSubmodule A D S x y n j))
    (fun j => ModuleCat.ofHom (lengthDifferential A D S x y n j)) i

/-- 長さ部分複体の最終 Hom への実際の chain map。 -/
def lengthInclusion (S : Set D) (x y : D) (n : ℕ) :
    lengthComplex A D S x y n ⟶ quotientHom A D S x y :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (lengthSubmodule A D S x y n i).subtype)
    (fun i => by rw [lengthComplex_d]; ext z; rfl)

instance lengthInclusion_mono (S : Set D) (x y : D) (n : ℕ) :
    Mono (lengthInclusion A D S x y n) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ =>
    (ModuleCat.mono_iff_injective _).2 (Submodule.subtype_injective _))

private lemma codRestrict_inclusion_naturality {V W : Type*}
    [AddCommGroup V] [AddCommGroup W] [Module A V] [Module A W]
    (f : V →ₗ[A] W) (P Q : Submodule A V) (R T : Submodule A W)
    (hPQ : P ≤ Q) (hRT : R ≤ T)
    (hP : ∀ z : P, f z ∈ R) (hQ : ∀ z : Q, f z ∈ T) :
    (LinearMap.codRestrict T (f.comp Q.subtype) hQ).comp (Submodule.inclusion hPQ) =
      (Submodule.inclusion hRT).comp (LinearMap.codRestrict R (f.comp P.subtype) hP) := by
  ext z
  rfl

lemma lengthDifferential_inclusion (S : Set D) (x y : D) {m n : ℕ} (hmn : m ≤ n) (i : ℤ) :
    (lengthDifferential A D S x y n i).comp
        (Submodule.inclusion (lengthSubmodule_mono A D S x y hmn i)) =
      (Submodule.inclusion (lengthSubmodule_mono A D S x y hmn (i + 1))).comp
        (lengthDifferential A D S x y m i) := by
  exact codRestrict_inclusion_naturality A _ _ _ _ _ _ _ _ _

/-- 長さの上限を増やすときの部分複体の包含。 -/
def lengthMap (S : Set D) (x y : D) {m n : ℕ} (hmn : m ≤ n) :
    lengthComplex A D S x y m ⟶ lengthComplex A D S x y n :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom
    (Submodule.inclusion (lengthSubmodule_mono A D S x y hmn i)))
    (fun i => by
      rw [lengthComplex_d, lengthComplex_d]
      exact ModuleCat.hom_ext (lengthDifferential_inclusion A D S x y hmn i))

@[reassoc] lemma lengthMap_inclusion (S : Set D) (x y : D) {m n : ℕ} (hmn : m ≤ n) :
    lengthMap A D S x y hmn ≫ lengthInclusion A D S x y n = lengthInclusion A D S x y m := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  exact Submodule.subtype_comp_inclusion (lengthSubmodule A D S x y m i)
    (lengthSubmodule A D S x y n i) (lengthSubmodule_mono A D S x y hmn i)

lemma lengthMap_refl (S : Set D) (x y : D) (n : ℕ) :
    lengthMap A D S x y (le_refl n) = 𝟙 (lengthComplex A D S x y n) := by
  apply (cancel_mono (lengthInclusion A D S x y n)).mp
  rw [lengthMap_inclusion, Category.id_comp]

lemma lengthMap_comp (S : Set D) (x y : D) {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    lengthMap A D S x y hmn ≫ lengthMap A D S x y hnp = lengthMap A D S x y (hmn.trans hnp) := by
  apply (cancel_mono (lengthInclusion A D S x y p)).mp
  rw [Category.assoc, lengthMap_inclusion, lengthMap_inclusion, lengthMap_inclusion]

/-- 消去作用素は filtration を一段下げる。n=0 では元の Hom 上の消去零性を含む。 -/
lemma lengthSubmodule_erasure (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    lengthSubmodule A D S x y n i ≤
      (lengthSubmodule A D S x y (n - 1) (i + 1)).comap
        ((erasure A D S x y).v i (i + 1) rfl).hom := by
  refine iSup_le (fun w => iSup_le (fun hw => ?_))
  rintro z ⟨t, rfl⟩
  change (erasure A D S x y).v i (i + 1) rfl ((ι A D S x y w).f i t) ∈
    lengthSubmodule A D S x y (n - 1) (i + 1)
  rw [erasure_path_apply]
  apply Submodule.sum_mem
  intro j hj
  have hlen := List.length_eraseIdx_add_one (Finset.mem_range.mp hj)
  exact path_mem_lengthSubmodule A D S x y (n - 1) (i + 1) (w.eraseIdx j) (by omega) _

/-- 各次数において長さ filtration の和は最終 Hom 全体である。 -/
lemma lengthSubmodule_exhaustive (S : Set D) (x y : D) (i : ℤ) :
    (⨆ n : ℕ, lengthSubmodule A D S x y n i) = ⊤ := by
  let P := ⨆ n : ℕ, lengthSubmodule A D S x y n i
  have hq : ModuleCat.ofHom P.mkQ = 0 := by
    apply (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : Word S => term A D w x y)).hom_ext
    rintro ⟨w⟩
    ext z
    change P.mkQ ((ι A D S x y w).f i z) = 0
    apply (Submodule.Quotient.mk_eq_zero P).2
    exact (le_iSup (fun n => lengthSubmodule A D S x y n i) w.length)
      (path_mem_lengthSubmodule A D S x y w.length i w le_rfl z)
  apply top_unique
  intro z _
  apply (Submodule.Quotient.mk_eq_zero P).1
  exact congrArg (fun f => f z) hq

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFiltration

/-! ## DerivedComparisonFiltrationZero（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFiltrationZero.lean） -/

/-! # 長さ filtration の零段と元の Hom の同型 -/

@[expose] public section DerivedComparisonFiltrationZero
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 内部 path 直和から空 path だけを取り出す chain map。 -/
def internalEmptyProjection (S : Set D) (x y : D) :
    internalHom A D S x y ⟶ homObject A D x y :=
  Sigma.desc (fun w : Word S => match w with
    | [] => 𝟙 _
    | _ :: _ => 0)

lemma originalHom_emptyProjection (S : Set D) (x y : D) :
    originalHom A D S x y ≫ internalEmptyProjection A D S x y = 𝟙 _ :=
  Sigma.ι_comp_desc _ _

lemma originalHom_f_injective (S : Set D) (x y : D) (i : ℤ) :
    Function.Injective ((originalHom A D S x y).f i) := by
  apply Function.LeftInverse.injective (g := (internalEmptyProjection A D S x y).f i)
  intro z
  have h := congrArg (fun f : homObject A D x y ⟶ homObject A D x y => f.f i z)
    (originalHom_emptyProjection A D S x y)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, HomologicalComplex.id_f,
    ModuleCat.id_apply] using h

/-- 零段の各次数は、元の Hom の次数ごとの像に等しい。 -/
lemma lengthSubmodule_zero (S : Set D) (x y : D) (i : ℤ) :
    lengthSubmodule A D S x y 0 i = LinearMap.range ((originalHom A D S x y).f i).hom := by
  apply le_antisymm
  · refine iSup_le (fun w => iSup_le (fun hw => ?_))
    have hw' : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    exact le_rfl
  · rintro z ⟨t, rfl⟩
    exact path_mem_lengthSubmodule A D S x y 0 i [] le_rfl t

def lengthZeroLinearMap (S : Set D) (x y : D) (i : ℤ) :
    (homObject A D x y).X i →ₗ[A] lengthSubmodule A D S x y 0 i :=
  LinearMap.codRestrict _ ((originalHom A D S x y).f i).hom
    (fun z => path_mem_lengthSubmodule A D S x y 0 i [] le_rfl z)

lemma lengthZeroLinearMap_coe (S : Set D) (x y : D) (i : ℤ)
    (z : (homObject A D x y).X i) :
    (lengthZeroLinearMap A D S x y i z).val = (originalHom A D S x y).f i z := rfl

lemma lengthZeroLinearMap_bijective (S : Set D) (x y : D) (i : ℤ) :
    Function.Bijective (lengthZeroLinearMap A D S x y i) := by
  constructor
  · intro z t h
    exact originalHom_f_injective A D S x y i (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    rw [lengthSubmodule_zero] at hz
    obtain ⟨t, ht⟩ := hz
    exact ⟨t, Subtype.ext ht⟩

lemma lengthZeroLinearMap_d (S : Set D) (x y : D) (i : ℤ) :
    (lengthDifferential A D S x y 0 i).comp (lengthZeroLinearMap A D S x y i) =
      (lengthZeroLinearMap A D S x y (i + 1)).comp ((homObject A D x y).d i (i + 1)).hom := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp only [LinearMap.comp_apply, lengthDifferential_coe, lengthZeroLinearMap_coe]
  have h := congrArg
    (fun f : (homObject A D x y).X i ⟶ (quotientHom A D S x y).X (i + 1) => f z)
    ((originalHomInclusion A D S x y).comm i (i + 1))
  simp only [ModuleCat.comp_apply, originalHomInclusion_f] at h
  convert h using 1

/-- 元の Hom を最終微分の零段へ入れる chain map。 -/
def lengthZeroMap (S : Set D) (x y : D) : homObject A D x y ⟶ lengthComplex A D S x y 0 :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (lengthZeroLinearMap A D S x y i))
    (fun i => by
      rw [lengthComplex_d]
      exact ModuleCat.hom_ext (lengthZeroLinearMap_d A D S x y i))

instance lengthZeroMap_isIso (S : Set D) (x y : D) : IsIso (lengthZeroMap A D S x y) := by
  have (i : ℤ) : IsIso ((lengthZeroMap A D S x y).f i) :=
    (LinearEquiv.toModuleIso (LinearEquiv.ofBijective (lengthZeroLinearMap A D S x y i)
      (lengthZeroLinearMap_bijective A D S x y i))).isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 零段は元の Hom 複体そのものである。 -/
def lengthZeroIso (S : Set D) (x y : D) : homObject A D x y ≅ lengthComplex A D S x y 0 :=
  asIso (lengthZeroMap A D S x y)

@[reassoc] lemma lengthZeroMap_inclusion (S : Set D) (x y : D) :
    lengthZeroMap A D S x y ≫ lengthInclusion A D S x y 0 = originalHomInclusion A D S x y := by
  ext i z
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFiltrationZero

/-! ## DerivedComparisonFiltrationColimit（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFiltrationColimit.lean） -/

/-! # 最終 dg 商 Hom は長さ部分複体の逐次余極限

各次数での有限長支持と、単射な包含の filtered colimit を用いる。
複体や Hom の有界性は仮定しない。
-/

@[expose] public section DerivedComparisonFiltrationColimit
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def lengthDiagram (S : Set D) (x y : D) : ℕ ⥤ Complex A where
  obj n := lengthComplex A D S x y n
  map f := lengthMap A D S x y (leOfHom f)
  map_id n := lengthMap_refl A D S x y n
  map_comp f g := (lengthMap_comp A D S x y (leOfHom f) (leOfHom g)).symm

/-- 全長さ部分複体の最終 Hom への包含 cocone。 -/
def lengthCocone (S : Set D) (x y : D) : Cocone (lengthDiagram A D S x y) where
  pt := quotientHom A D S x y
  ι.app n := lengthInclusion A D S x y n
  ι.naturality {m n} f := by
    change lengthMap A D S x y (leOfHom f) ≫ lengthInclusion A D S x y n =
      lengthInclusion A D S x y m ≫ 𝟙 _
    rw [Category.comp_id]
    exact lengthMap_inclusion A D S x y (leOfHom f)

lemma exists_lengthSubmodule (S : Set D) (x y : D) (i : ℤ)
    (z : (internalHom A D S x y).X i) : ∃ n : ℕ, z ∈ lengthSubmodule A D S x y n i := by
  have hz : z ∈ ⨆ n : ℕ, lengthSubmodule A D S x y n i := by
    rw [lengthSubmodule_exhaustive]
    trivial
  exact (Submodule.mem_iSup_of_directed _
    (fun m n => ⟨max m n, lengthSubmodule_mono A D S x y (le_max_left m n) i,
      lengthSubmodule_mono A D S x y (le_max_right m n) i⟩)).1 hz

/-- 各次数で、長さの単射な包含の cocone は余極限。 -/
def lengthCocone_eval_isColimit (S : Set D) (x y : D) (i : ℤ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i).mapCocone
      (lengthCocone A D S x y)) := by
  have : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (forget (ModuleCat.{u} A))
  apply isColimitOfReflects (forget (ModuleCat.{u} A))
  apply Types.FilteredColimit.isColimitOf'
  · intro z
    obtain ⟨n, hn⟩ := exists_lengthSubmodule A D S x y i z
    exact ⟨n, ⟨z, hn⟩, rfl⟩
  · intro n z t h
    have ht : z = t := Subtype.ext h
    exact ⟨n, 𝟙 n, by rw [ht]⟩

/-- 最終微分を含む Hom 全体を、有界長部分複体の逐次余極限として復元する。 -/
def lengthCocone_isColimit (S : Set D) (x y : D) : IsColimit (lengthCocone A D S x y) :=
  HomologicalComplex.isColimitOfEval _ _ (lengthCocone_eval_isColimit A D S x y)

def lengthColimitIso (S : Set D) (x y : D) :
    colimit (lengthDiagram A D S x y) ≅ quotientHom A D S x y :=
  (colimit.isColimit _).coconePointUniqueUpToIso (lengthCocone_isColimit A D S x y)

@[reassoc] lemma lengthColimitIso_ι (S : Set D) (x y : D) (n : ℕ) :
    colimit.ι (lengthDiagram A D S x y) n ≫ (lengthColimitIso A D S x y).hom =
      lengthInclusion A D S x y n :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ n

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFiltrationColimit

/-! ## DerivedComparisonFunctoriality（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFunctoriality.lean） -/

/-! # 指定部分集合を対応させる dg 関手の、明示的商への延長 -/

@[expose] public section DerivedComparisonFunctoriality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
  (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)

/-- 対象の対応により、標的商の標準 ε を収縮データとして指定する。 -/
def functorContracted : ContractedFunctor A D S (QuotientObject E T) where
  toDGFunctor := F.comp (inclusion A E T)
  homotopy b := epsilonElement A E T ⟨F.obj b.val, hF b.val b.property⟩
  d_homotopy b := differential_epsilonElement A E T ⟨F.obj b.val, hF b.val b.property⟩

/-- 固定した ε を保つ、明示的 dg 商間の実際の関手。 -/
def quotientDGFunctor : DGFunctor A (QuotientObject D S) (QuotientObject E T) :=
  extension A (functorContracted A D E F S T hF)

lemma quotientDGFunctor_obj (x : QuotientObject D S) :
    (quotientDGFunctor A D E F S T hF).obj x = ⟨F.obj x.val⟩ := rfl

/-- 元の dg 圏の包含と、商への延長は厳密に可換する。 -/
lemma quotientDGFunctor_inclusion :
    (inclusion A D S).comp (quotientDGFunctor A D E F S T hF) =
      F.comp (inclusion A E T) :=
  inclusion_comp_extension A (functorContracted A D E F S T hF)

lemma quotientDGFunctor_epsilon (b : S) :
    ((quotientDGFunctor A D E F S T hF).map ⟨b.val⟩ ⟨b.val⟩).f (-1)
        (epsilonElement A D S b) =
      epsilonElement A E T ⟨F.obj b.val, hF b.val b.property⟩ :=
  restrict_extension_homotopy A (functorContracted A D E F S T hF) b
end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFunctoriality

/-! ## DerivedComparisonColimitQuasiIso（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonColimitQuasiIso.lean） -/

/-! # 厳密な複体図式の exact な余極限による擬同型の保存

ホモトピー圏内だけで与えられた図式には、この補題を適用しない。
-/

@[expose] public section DerivedComparisonColimitQuasiIso
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
  [Small.{u} J] [HasColimitsOfShape J (ModuleCat.{u} A)]
  [HasExactColimitsOfShape J (ModuleCat.{u} A)]

def complexTransposeMap {F G : J ⥤ Complex A} (α : F ⟶ G) :
    complexDiagramTranspose A F ⟶ complexDiagramTranspose A G where
  f i := Functor.whiskerRight α (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
  comm' i j _ := by
    apply NatTrans.ext
    funext k
    exact (α.app k).comm i j

omit [Small.{u} J] [HasColimitsOfShape J (ModuleCat.{u} A)]
  [HasExactColimitsOfShape J (ModuleCat.{u} A)] in
lemma complexTransposeMap_quasiIso {F G : J ⥤ Complex A} (α : F ⟶ G)
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (complexTransposeMap A α) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro j
  exact hα j

/-- 次数ごとの余極限で構成した複体と、指定された複体の余極限との同型。 -/
def complexColimitComparison (F : J ⥤ Complex A) :
    ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).obj
      (complexDiagramTranspose A F) ≅ colimit F :=
  (isColimitCoconeOfHasColimitEval F).coconePointUniqueUpToIso (colimit.isColimit F)

@[reassoc] lemma complexColimitComparison_ι (F : J ⥤ Complex A) (j : J) :
    (coconeOfHasColimitEval F).ι.app j ≫ (complexColimitComparison A F).hom = colimit.ι F j :=
  (isColimitCoconeOfHasColimitEval F).comp_coconePointUniqueUpToIso_hom _ j

lemma complexColimitComparison_naturality {F G : J ⥤ Complex A} (α : F ⟶ G) :
    (complexColimitComparison A F).hom ≫ colimMap α =
      ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).map
        (complexTransposeMap A α) ≫ (complexColimitComparison A G).hom := by
  apply (isColimitCoconeOfHasColimitEval F).hom_ext
  intro j
  rw [← Category.assoc, complexColimitComparison_ι, ι_colimMap, ← Category.assoc]
  have h : (coconeOfHasColimitEval F).ι.app j ≫
      ((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).map
        (complexTransposeMap A α) = α.app j ≫ (coconeOfHasColimitEval G).ι.app j := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact ι_colimMap (Functor.whiskerRight α
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)) j
  rw [h, Category.assoc, complexColimitComparison_ι]

/-- 対象ごと擬同型な厳密自然変換は、exact な余極限でも擬同型となる。 -/
lemma complex_colimMap_quasiIso {F G : J ⥤ Complex A} (α : F ⟶ G)
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (colimMap α) := by
  have : (colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).Additive :=
    { map_add := by
        intro F G α β
        apply colimit.hom_ext
        intro j
        change colimit.ι F j ≫ colimMap (α + β) =
          colimit.ι F j ≫ (colimMap α + colimMap β)
        rw [ι_colimMap, Preadditive.comp_add, ι_colimMap, ι_colimMap]
        exact Preadditive.add_comp _ _ _ (α.app j) (β.app j) (colimit.ι G j) }
  have : QuasiIso (complexTransposeMap A α) := complexTransposeMap_quasiIso A α hα
  have : QuasiIso
      (((colim : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).map
        (complexTransposeMap A α)) := inferInstance
  have he := complexColimitComparison_naturality A α
  have : QuasiIso ((complexColimitComparison A F).hom ≫ colimMap α) := by
    rw [he]
    infer_instance
  exact quasiIso_of_comp_left (complexColimitComparison A F).hom (colimMap α)

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonColimitQuasiIso

/-! ## DerivedComparisonGradedProjection（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonGradedProjection.lean） -/

/-! # 固定長 path 直和の射影と最終微分との整合性 -/

@[expose] public section DerivedComparisonGradedProjection
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
attribute [local instance] Classical.propDecidable

/-- 指定条件を満たす word の内部 path 項だけの直和。 -/
abbrev selectedHom (S : Set D) (P : Word S → Prop) (x y : D) : Complex A :=
  ∐ (fun w : {w : Word S // P w} => term A D w.val x y)

def selectedInclusion (S : Set D) (P : Word S → Prop) (x y : D) :
    selectedHom A D S P x y ⟶ internalHom A D S x y :=
  Sigma.desc (fun w => ι A D S x y w.val)

def selectedProjection (S : Set D) (P : Word S → Prop) (x y : D) :
    internalHom A D S x y ⟶ selectedHom A D S P x y := by
  classical
  exact Sigma.desc (fun w => if h : P w then
    Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x y) ⟨w, h⟩ else 0)

@[reassoc] lemma selected_ι_inclusion (S : Set D) (P : Word S → Prop) (x y : D)
    (w : {w : Word S // P w}) :
    Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x y) w ≫
      selectedInclusion A D S P x y = ι A D S x y w.val := Sigma.ι_comp_desc _ _

lemma ι_selectedProjection (S : Set D) (P : Word S → Prop) (x y : D) (w : Word S) :
    ι A D S x y w ≫ selectedProjection A D S P x y =
      if h : P w then
        Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x y) ⟨w, h⟩ else 0 := by
  classical
  exact Sigma.ι_comp_desc _ _

lemma selectedInclusion_projection (S : Set D) (P : Word S → Prop) (x y : D) :
    selectedInclusion A D S P x y ≫ selectedProjection A D S P x y = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro w
  rw [← Category.assoc, selected_ι_inclusion, ι_selectedProjection, dite_eq_left w.property,
    Category.comp_id]

/-- 指定した全 word の長さが n 以下なら、その直和の像は第 n 段階に属する。 -/
lemma selectedInclusion_mem_length (S : Set D) (P : Word S → Prop) (x y : D) (n : ℕ)
    (hP : ∀ w, P w → w.length ≤ n) (i : ℤ) (z : (selectedHom A D S P x y).X i) :
    (selectedInclusion A D S P x y).f i z ∈ lengthSubmodule A D S x y n i := by
  let F := lengthSubmodule A D S x y n i
  have hq : (selectedInclusion A D S P x y).f i ≫ ModuleCat.ofHom F.mkQ = 0 := by
    apply (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : {w : Word S // P w} => term A D w.val x y)).hom_ext
    rintro ⟨w⟩
    have h := congrArg (fun f => f.f i) (selected_ι_inclusion A D S P x y w)
    simp only [HomologicalComplex.comp_f] at h
    change (Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x y) w).f i ≫
      ((selectedInclusion A D S P x y).f i ≫ ModuleCat.ofHom F.mkQ) = _
    rw [← Category.assoc, h]
    ext t
    exact (Submodule.Quotient.mk_eq_zero F).2
      (path_mem_lengthSubmodule A D S x y n i w.val (hP w.val w.property) t)
  apply (Submodule.Quotient.mk_eq_zero F).1
  exact congrArg (fun f => f z) hq

abbrev fixedLengthHom (S : Set D) (x y : D) (n : ℕ) : Complex A :=
  selectedHom A D S (fun w => w.length = n) x y

abbrev fixedLengthInclusion (S : Set D) (x y : D) (n : ℕ) :
    fixedLengthHom A D S x y n ⟶ internalHom A D S x y :=
  selectedInclusion A D S (fun w => w.length = n) x y

abbrev fixedLengthProjection (S : Set D) (x y : D) (n : ℕ) :
    internalHom A D S x y ⟶ fixedLengthHom A D S x y n :=
  selectedProjection A D S (fun w => w.length = n) x y

/-- 長さ n+1 への射影は n 以下の部分加群を消す。 -/
lemma fixedLengthProjection_kills_lower (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    lengthSubmodule A D S x y n i ≤
      LinearMap.ker ((fixedLengthProjection A D S x y (n + 1)).f i).hom := by
  classical
  refine iSup_le (fun w => iSup_le (fun hw => ?_))
  rintro z ⟨t, rfl⟩
  have he : w.length ≠ n + 1 := by omega
  have h := congrArg (fun f => f.f i t)
    (ι_selectedProjection A D S (fun w => w.length = n + 1) x y w)
  simp only [dite_eq_right he, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    HomologicalComplex.zero_f] at h
  exact h

/-- 最終微分の消去部分は、固定長への射影の下で零となる。 -/
lemma fixedLengthProjection_erasure (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : lengthSubmodule A D S x y (n + 1) i) :
    (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
      ((erasure A D S x y).v i (i + 1) rfl z.val) = 0 := by
  have hz := lengthSubmodule_erasure A D S x y (n + 1) i z.property
  exact fixedLengthProjection_kills_lower A D S x y n (i + 1) hz

/-- 最終微分を持つ第 n+1 段階から、内部微分だけの固定長直和への射影。 -/
def lengthLayerProjection (S : Set D) (x y : D) (n : ℕ) :
    lengthComplex A D S x y (n + 1) ⟶ fixedLengthHom A D S x y (n + 1) :=
  CochainComplex.ofHom (fun i =>
    ModuleCat.ofHom (lengthSubmodule A D S x y (n + 1) i).subtype ≫
      (fixedLengthProjection A D S x y (n + 1)).f i) (fun i => by
        rw [lengthComplex_d]
        ext z
        change (fixedLengthHom A D S x y (n + 1)).d i (i + 1)
          ((fixedLengthProjection A D S x y (n + 1)).f i z.val) =
          (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
            (lengthDifferential A D S x y (n + 1) i z).val
        rw [lengthDifferential_coe]
        have h := congrArg (fun f => f z.val)
          ((fixedLengthProjection A D S x y (n + 1)).comm i (i + 1))
        simp only [ModuleCat.comp_apply] at h
        rw [h]
        change (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
          ((internalHom A D S x y).d i (i + 1) z.val) =
          (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
            ((quotientHom A D S x y).d i (i + 1) z.val)
        rw [quotientHom_d]
        change _ = (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
          ((internalHom A D S x y).d i (i + 1) z.val +
            (erasure A D S x y).v i (i + 1) rfl z.val)
        rw [map_add, fixedLengthProjection_erasure, add_zero])

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonGradedProjection

/-! ## DerivedComparisonGraded（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonGraded.lean） -/

/-! # 長さ filtration の随伴次数部分と固定長 path 直和 -/

@[expose] public section DerivedComparisonGraded
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
attribute [local instance] Classical.propDecidable

/-- 内部微分の直和上で、長さ n 以下だけを残す射影。 -/
def lengthCutoff (S : Set D) (x y : D) (n : ℕ) : internalHom A D S x y ⟶ internalHom A D S x y :=
  selectedProjection A D S (fun w => w.length ≤ n) x y ≫
    selectedInclusion A D S (fun w => w.length ≤ n) x y

lemma ι_lengthCutoff (S : Set D) (x y : D) (n : ℕ) (w : Word S) :
    ι A D S x y w ≫ lengthCutoff A D S x y n =
      if w.length ≤ n then ι A D S x y w else 0 := by
  rw [lengthCutoff, ← Category.assoc, ι_selectedProjection]
  by_cases h : w.length ≤ n
  · rw [dite_eq_left h, ite_eq_left h, selected_ι_inclusion]
  · rw [dite_eq_right h, ite_eq_right h, zero_comp]

lemma lengthCutoff_mem (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : (internalHom A D S x y).X i) :
    (lengthCutoff A D S x y n).f i z ∈ lengthSubmodule A D S x y n i :=
  selectedInclusion_mem_length A D S (fun w => w.length ≤ n) x y n (fun _ h => h) i _

lemma lengthCutoff_fixed (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : (internalHom A D S x y).X i) (hz : z ∈ lengthSubmodule A D S x y n i) :
    (lengthCutoff A D S x y n).f i z = z := by
  have hle : lengthSubmodule A D S x y n i ≤
      LinearMap.ker (((lengthCutoff A D S x y n).f i).hom - LinearMap.id) := by
    refine iSup_le (fun w => iSup_le (fun hw => ?_))
    rintro t ⟨v, rfl⟩
    have h := congrArg (fun f => f.f i v) (ι_lengthCutoff A D S x y n w)
    simp only [ite_eq_left hw, HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp (hle hz)

lemma ι_fixedLengthProjector (S : Set D) (x y : D) (n : ℕ) (w : Word S) :
    ι A D S x y w ≫
        (fixedLengthProjection A D S x y n ≫ fixedLengthInclusion A D S x y n) =
      if w.length = n then ι A D S x y w else 0 := by
  rw [← Category.assoc, ι_selectedProjection]
  by_cases h : w.length = n
  · rw [dite_eq_left h, ite_eq_left h, selected_ι_inclusion]
  · rw [dite_eq_right h, ite_eq_right h, zero_comp]

/-- 相隣る cutoff の差は、その固定長成分への射影である。 -/
lemma lengthCutoff_succ (S : Set D) (x y : D) (n : ℕ) :
    lengthCutoff A D S x y (n + 1) = lengthCutoff A D S x y n +
      fixedLengthProjection A D S x y (n + 1) ≫ fixedLengthInclusion A D S x y (n + 1) := by
  apply Sigma.hom_ext
  intro w
  change ι A D S x y w ≫ lengthCutoff A D S x y (n + 1) =
    ι A D S x y w ≫ (lengthCutoff A D S x y n +
      fixedLengthProjection A D S x y (n + 1) ≫ fixedLengthInclusion A D S x y (n + 1))
  rw [Preadditive.comp_add, ι_lengthCutoff, ι_lengthCutoff, ι_fixedLengthProjector]
  by_cases h : w.length ≤ n
  · have hn : w.length ≤ n + 1 := by omega
    have he : w.length ≠ n + 1 := by omega
    rw [ite_eq_left hn, ite_eq_left h, ite_eq_right he, add_zero]
  · by_cases he : w.length = n + 1
    · have hn : w.length ≤ n + 1 := by omega
      rw [ite_eq_left hn, ite_eq_right h, ite_eq_left he, zero_add]
    · have hn : ¬ w.length ≤ n + 1 := by omega
      rw [ite_eq_right hn, ite_eq_right h, ite_eq_right he, add_zero]

/-- 固定長射影の核は、ちょうど一段前の filtration である。 -/
lemma lengthLayerProjection_kernel (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : lengthSubmodule A D S x y (n + 1) i) :
    (lengthLayerProjection A D S x y n).f i z = 0 ↔
      z.val ∈ lengthSubmodule A D S x y n i := by
  constructor
  · intro hz
    have hp : (fixedLengthProjection A D S x y (n + 1)).f i z.val = 0 := hz
    have h := congrArg (fun f => f.f i z.val) (lengthCutoff_succ A D S x y n)
    change (lengthCutoff A D S x y (n + 1)).f i z.val =
      (lengthCutoff A D S x y n).f i z.val +
        (fixedLengthInclusion A D S x y (n + 1)).f i
          ((fixedLengthProjection A D S x y (n + 1)).f i z.val) at h
    rw [hp, map_zero, add_zero] at h
    rw [lengthCutoff_fixed A D S x y (n + 1) i z.val z.property] at h
    rw [h]
    exact lengthCutoff_mem A D S x y n i z.val
  · intro hz
    exact fixedLengthProjection_kills_lower A D S x y n i hz

lemma lengthLayerProjection_surjective (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    Function.Surjective ((lengthLayerProjection A D S x y n).f i) := by
  intro z
  let t : lengthSubmodule A D S x y (n + 1) i :=
    ⟨(fixedLengthInclusion A D S x y (n + 1)).f i z,
      selectedInclusion_mem_length A D S (fun w => w.length = n + 1) x y (n + 1)
        (fun _ h => h.le) i z⟩
  refine ⟨t, ?_⟩
  have h := congrArg (fun f => f.f i z)
    (selectedInclusion_projection A D S (fun w => w.length = n + 1) x y)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, HomologicalComplex.id_f,
    ModuleCat.id_apply] at h
  convert h using 1
  rfl

private lemma inclusion_exact_of_kernel {V W : Type*}
    [AddCommGroup V] [AddCommGroup W] [Module A V] [Module A W]
    (P Q : Submodule A V) (hPQ : P ≤ Q) (g : Q →ₗ[A] W)
    (h : ∀ z : Q, g z = 0 ↔ z.val ∈ P) : Function.Exact (Submodule.inclusion hPQ) g := by
  intro z
  rw [h]
  constructor
  · intro hz
    exact ⟨⟨z.val, hz⟩, Subtype.ext rfl⟩
  · rintro ⟨t, rfl⟩
    exact t.property

lemma lengthLayerProjection_exact (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    Function.Exact ((lengthMap A D S x y (Nat.le_succ n)).f i).hom
      ((lengthLayerProjection A D S x y n).f i).hom := by
  exact inclusion_exact_of_kernel A _ _
    (lengthSubmodule_mono A D S x y (Nat.le_succ n) i) _
    (lengthLayerProjection_kernel A D S x y n i)

lemma lengthMap_layerProjection (S : Set D) (x y : D) (n : ℕ) :
    lengthMap A D S x y (Nat.le_succ n) ≫ lengthLayerProjection A D S x y n = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact ModuleCat.hom_ext (lengthLayerProjection_exact A D S x y n i).linearMap_comp_eq_zero

/-- 固定長直和を第三項とする実際の短複体。 -/
def lengthLayerShortComplex (S : Set D) (x y : D) (n : ℕ) : ShortComplex (Complex A) :=
  ShortComplex.mk (lengthMap A D S x y (Nat.le_succ n)) (lengthLayerProjection A D S x y n)
    (lengthMap_layerProjection A D S x y n)

/-- 各次数で固定長 path への射影は、前段階の包含の cokernel である。 -/
def lengthLayer_eval_isColimit (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    IsColimit (CokernelCofork.ofπ ((lengthLayerProjection A D S x y n).f i)
      (show (lengthMap A D S x y (Nat.le_succ n)).f i ≫
          (lengthLayerProjection A D S x y n).f i = 0 from
        congrArg (fun f => f.f i) (lengthMap_layerProjection A D S x y n))) :=
  ModuleCat.isColimitCokernelCofork _ _ (lengthLayerProjection_exact A D S x y n i)
    (lengthLayerProjection_surjective A D S x y n i)

/-- 複体としても、固定長直和は相隣る長さ部分複体の cokernel。 -/
def lengthLayer_isColimit (S : Set D) (x y : D) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (lengthLayerProjection A D S x y n)
      (lengthMap_layerProjection A D S x y n)) := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  exact (isColimitMapCoconeCoforkEquiv'
    (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
    (lengthMap_layerProjection A D S x y n)).symm (lengthLayer_eval_isColimit A D S x y n i)

/-- 正の随伴次数部分の、内部微分を持つ固定長 path 直和としての計算。 -/
def lengthGradedIso (S : Set D) (x y : D) (n : ℕ) :
    cokernel (lengthMap A D S x y (Nat.le_succ n)) ≅ fixedLengthHom A D S x y (n + 1) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (lengthLayer_isColimit A D S x y n)

/-- 相隣る filtration と固定長直和は、複体の短完全列をなす。 -/
lemma lengthLayer_shortExact (S : Set D) (x y : D) (n : ℕ) :
    (lengthLayerShortComplex A D S x y n).ShortExact := by
  have hm : Mono (lengthMap A D S x y (Nat.le_succ n)) :=
    mono_of_mono_fac (lengthMap_inclusion A D S x y (Nat.le_succ n))
  have hc := lengthLayer_isColimit A D S x y n
  exact
    { exact := (lengthLayerShortComplex A D S x y n).exact_of_g_is_cokernel hc
      mono_f := hm
      epi_g := epi_of_isColimit_cofork hc }

@[reassoc] lemma lengthGradedIso_π (S : Set D) (x y : D) (n : ℕ) :
    cokernel.π (lengthMap A D S x y (Nat.le_succ n)) ≫ (lengthGradedIso A D S x y n).hom =
      lengthLayerProjection A D S x y n :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonGraded

/-! ## DerivedComparisonFiltrationAction（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonFiltrationAction.lean） -/

/-! # 長さ filtration と先頭 Hom の全次数作用

word を変えない部分直和への作用と射影の可換式から、最終微分を持つ各段階の安定性を得る。
-/

@[expose] public section DerivedComparisonFiltrationAction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
attribute [local instance] Classical.propDecidable

/-- word 条件を保つ先頭 Hom の作用。 -/
def selectedPrepend (S : Set D) (P : Word S → Prop) (x y z : D) :
    homObject A D x y ⊗ selectedHom A D S P y z ⟶ selectedHom A D S P x z :=
  (tensorLeftCoproductIsColimit (homObject A D x y)
    (fun w : {w : Word S // P w} => term A D w.val y z)).desc
      (Cofan.mk _ (fun w => prependMap A D w.val x y z ≫
        Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x z) w))

@[reassoc] lemma selectedPrepend_ι (S : Set D) (P : Word S → Prop) (x y z : D)
    (w : {w : Word S // P w}) :
    (homObject A D x y ◁ Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y z) w) ≫
        selectedPrepend A D S P x y z =
      prependMap A D w.val x y z ≫
        Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x z) w :=
  (tensorLeftCoproductIsColimit (homObject A D x y) _).fac _ ⟨w⟩

/-- 選んだ path の包含は、先頭 Hom の作用と可換。 -/
lemma selectedPrepend_inclusion (S : Set D) (P : Word S → Prop) (x y z : D) :
    selectedPrepend A D S P x y z ≫ selectedInclusion A D S P x z =
      (homObject A D x y ◁ selectedInclusion A D S P y z) ≫ internalPrepend A D S x y z := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y)
    (fun w : {w : Word S // P w} => term A D w.val y z)).hom_ext
  rintro ⟨w⟩
  change (homObject A D x y ◁
      Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y z) w) ≫
      (selectedPrepend A D S P x y z ≫ selectedInclusion A D S P x z) =
    (homObject A D x y ◁
      Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y z) w) ≫
      ((homObject A D x y ◁ selectedInclusion A D S P y z) ≫ internalPrepend A D S x y z)
  rw [← Category.assoc, selectedPrepend_ι, Category.assoc, selected_ι_inclusion,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, selected_ι_inclusion,
    internalPrepend_ι]

/-- 選んだ path への射影も、先頭 Hom の作用と可換。 -/
lemma selectedProjection_prepend (S : Set D) (P : Word S → Prop) (x y z : D) :
    internalPrepend A D S x y z ≫ selectedProjection A D S P x z =
      (homObject A D x y ◁ selectedProjection A D S P y z) ≫ selectedPrepend A D S P x y z := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y)
    (fun w : Word S => term A D w y z)).hom_ext
  rintro ⟨w⟩
  change (homObject A D x y ◁ ι A D S y z w) ≫
      (internalPrepend A D S x y z ≫ selectedProjection A D S P x z) =
    (homObject A D x y ◁ ι A D S y z w) ≫
      ((homObject A D x y ◁ selectedProjection A D S P y z) ≫ selectedPrepend A D S P x y z)
  rw [← Category.assoc, internalPrepend_ι, Category.assoc, ι_selectedProjection,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ι_selectedProjection]
  by_cases h : P w
  · rw [dite_eq_left h, dite_eq_left h, selectedPrepend_ι]
  · rw [dite_eq_right h, dite_eq_right h, comp_zero,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]

/-- 長さ cutoff は先頭 Hom の作用と可換である。 -/
lemma lengthCutoff_prepend (S : Set D) (x y z : D) (n : ℕ) :
    internalPrepend A D S x y z ≫ lengthCutoff A D S x z n =
      (homObject A D x y ◁ lengthCutoff A D S y z n) ≫ internalPrepend A D S x y z := by
  simp only [lengthCutoff, ← Category.assoc, selectedProjection_prepend]
  rw [Category.assoc, selectedPrepend_inclusion, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp]

/-- 内部先頭作用は、相手の Hom の長さ上限を保つ。作用する Hom の次数は任意。 -/
lemma internalPrepend_mem_length (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) (f : (homObject A D x y).X p)
    (t : (internalHom A D S y z).X q) (ht : t ∈ lengthSubmodule A D S y z n q) :
    (internalPrepend A D S x y z).f r
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr (f ⊗ₜ[A] t)) ∈
        lengthSubmodule A D S x z n r := by
  have h := congrArg (fun g => g.f r
    (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr (f ⊗ₜ[A] t)))
    (lengthCutoff_prepend A D S x y z n)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  rw [whiskerLeft_apply, lengthCutoff_fixed A D S y z n q t ht] at h
  rw [← h]
  exact lengthCutoff_mem A D S x z n r _

/-- 最終微分についての先頭作用も、全ての斉次次数で長さ上限を保つ。 -/
lemma quotientPrepend_mem_length (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) (f : (homObject A D x y).X p)
    (t : (quotientHom A D S y z).X q) (ht : t ∈ lengthSubmodule A D S y z n q) :
    (quotientPrepend A D S x y z).f r
      (ιTensorObj (homObject A D x y) (quotientHom A D S y z) p q r hr (f ⊗ₜ[A] t)) ∈
        lengthSubmodule A D S x z n r := by
  have h := congrArg (fun g => g (f ⊗ₜ[A] t)) (quotientPrepend_ι A D S x y z p q r hr)
  simp only [ModuleCat.comp_apply] at h
  have hm := internalPrepend_mem_length A D S x y z n p q r hr f t ht
  exact (congrArg (fun v => v ∈ lengthSubmodule A D S x z n r) h).mpr hm

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonFiltrationAction

/-! ## DerivedComparisonLengthAction（旧 SerrePositivity/DifferentialGraded/Quotient/DerivedComparisonLengthAction.lean） -/

/-! # 長さ部分複体への全次数作用の制限

純粋 tensor 上の安定性と最終微分の Leibniz 則から、実際の chain map を作る。
-/

@[expose] public section DerivedComparisonLengthAction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable (A : Type u) [CommRing A]

/-- 純粋 tensor 上で部分加群を保つ線形写像の制限。 -/
def tensorCodRestrict {V W T : Type u}
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Module A V] [Module A W] [Module A T]
    (P : Submodule A W) (Q : Submodule A T) (g : V ⊗[A] W →ₗ[A] T)
    (hg : ∀ a (b : P), g (a ⊗ₜ[A] b.val) ∈ Q) : V ⊗[A] P →ₗ[A] Q :=
  LinearMap.codRestrict Q (g.comp (TensorProduct.map LinearMap.id P.subtype)) (by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simpa using hg a b
    | add t t' ht ht' => simpa only [map_add] using Q.add_mem ht ht')

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 長さ n の部分加群へ制限した双次数の先頭作用。 -/
def lengthPrependComponent (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) :
    (homObject A D x y).X p ⊗ (lengthComplex A D S y z n).X q ⟶
      (lengthComplex A D S x z n).X r :=
  ModuleCat.ofHom (tensorCodRestrict A (lengthSubmodule A D S y z n q)
    (lengthSubmodule A D S x z n r)
    ((ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr ≫
      (internalPrepend A D S x y z).f r).hom)
    (fun a b => internalPrepend_mem_length A D S x y z n p q r hr a b.val b.property))

lemma lengthPrependComponent_coe (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) (f : (homObject A D x y).X p)
    (t : (lengthComplex A D S y z n).X q) :
    (lengthPrependComponent A D S x y z n p q r hr (f ⊗ₜ[A] t)).val =
      (internalPrepend A D S x y z).f r
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr
          (f ⊗ₜ[A] t.val)) := by
  change (internalPrepend A D S x y z).f r
    (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr
      ((TensorProduct.map (LinearMap.id : (homObject A D x y).X p →ₗ[A] _)
        (lengthSubmodule A D S y z n q).subtype) (f ⊗ₜ[A] t))) = _
  rw [TensorProduct.map_tmul]
  rfl

lemma lengthPrependComponent_d (S : Set D) (x y z : D) (n : ℕ) (p q : ℤ) :
    lengthPrependComponent A D S x y z n p q (p + q) rfl ≫
        (lengthComplex A D S x z n).d (p + q) (p + q + 1) =
      ((homObject A D x y).d p (p + 1) ▷ (lengthComplex A D S y z n).X q) ≫
        lengthPrependComponent A D S x y z n (p + 1) q (p + q + 1) (by omega) +
      p.negOnePow • (((homObject A D x y).X p ◁
          (lengthComplex A D S y z n).d q (q + 1)) ≫
        lengthPrependComponent A D S x y z n p (q + 1) (p + q + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f t
  rw [lengthComplex_d, lengthComplex_d]
  apply Subtype.ext
  change (lengthDifferential A D S x z n (p + q)
      (lengthPrependComponent A D S x y z n p q (p + q) rfl (f ⊗ₜ[A] t))).val =
    (lengthPrependComponent A D S x y z n (p + 1) q (p + q + 1) (by omega)
      ((homObject A D x y).d p (p + 1) f ⊗ₜ[A] t)).val +
    p.negOnePow • (lengthPrependComponent A D S x y z n p (q + 1) (p + q + 1) (by omega)
      (f ⊗ₜ[A] lengthDifferential A D S y z n q t)).val
  simp only [lengthDifferential_coe, lengthPrependComponent_coe]
  exact internalPrepend_total_d_apply A D S x y z p q (p + q) rfl f t.val

/-- 最終微分を持つ長さ部分複体への先頭作用。 -/
def lengthPrepend (S : Set D) (x y z : D) (n : ℕ) :
    homObject A D x y ⊗ lengthComplex A D S y z n ⟶ lengthComplex A D S x z n :=
  tensorLift (lengthPrependComponent A D S x y z n)
    (lengthPrependComponent_d A D S x y z n)

@[reassoc] lemma lengthPrepend_ι (S : Set D) (x y z : D) (n : ℕ)
    (p q r : ℤ) (hr : p + q = r) :
    ιTensorObj (homObject A D x y) (lengthComplex A D S y z n) p q r hr ≫
        (lengthPrepend A D S x y z n).f r =
      lengthPrependComponent A D S x y z n p q r hr :=
  ι_tensorLift _ _ p q r hr

/-- 長さ部分複体の包含は、最終微分についての先頭作用と可換。 -/
@[reassoc] lemma lengthPrepend_inclusion (S : Set D) (x y z : D) (n : ℕ) :
    lengthPrepend A D S x y z n ≫ lengthInclusion A D S x z n =
      (homObject A D x y ◁ lengthInclusion A D S y z n) ≫ quotientPrepend A D S x y z := by
  apply tensorHom_ext
  intro p q r hr
  rw [HomologicalComplex.comp_f, ← Category.assoc, lengthPrepend_ι,
    HomologicalComplex.comp_f, ← Category.assoc, ι_whiskerLeft, Category.assoc,
    quotientPrepend_ι]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f t
  change (lengthPrependComponent A D S x y z n p q r hr (f ⊗ₜ[A] t)).val = _
  rw [lengthPrependComponent_coe]
  rfl

/-- 長さの上限を増やす包含は、制限した全次数作用と可換。 -/
lemma lengthPrepend_map (S : Set D) (x y z : D) {m n : ℕ} (hmn : m ≤ n) :
    lengthPrepend A D S x y z m ≫ lengthMap A D S x z hmn =
      (homObject A D x y ◁ lengthMap A D S y z hmn) ≫ lengthPrepend A D S x y z n := by
  apply (cancel_mono (lengthInclusion A D S x z n)).mp
  rw [Category.assoc, lengthMap_inclusion, lengthPrepend_inclusion, Category.assoc,
    lengthPrepend_inclusion, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    lengthMap_inclusion]

end SerrePositivity.DifferentialGraded.DGQuotient
end

end DerivedComparisonLengthAction

/-! ## FunctorLaws（旧 SerrePositivity/DifferentialGraded/Quotient/FunctorLaws.lean） -/

/-!
概要：固定標準 ε を保つ正本商関手の、厳密な恒等・合成と元 Hom 作用。
方針：同じ指定収縮付き普遍性で関手全体を照合する。
規約：関手変数の任意の自然変換の延長は主張しない。
使われ方：ε 整合関手圏の横の単位・合成則。
-/

@[expose] public noncomputable section FunctorLaws
universe u v w t s

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
private lemma functorAssoc {R : Type u} [CommRing R]
    {X : Type v} {Y : Type w} {Z : Type t} {W : Type s}
    [DGCategory R X] [DGCategory R Y] [DGCategory R Z] [DGCategory R W]
    (a : DGFunctor R X Y) (b : DGFunctor R Y Z) (c : DGFunctor R Z W) :
    (a.comp b).comp c = a.comp (b.comp c) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, eqToHom_refl,
    Category.comp_id, Category.assoc]

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

/-- 正本商関手は元の恒等関手を厳密に保つ。 -/
lemma quotientDGFunctor_id (S : Set C) :
    quotientDGFunctor R C C (DGFunctor.id C) S S (fun _ hx => hx) =
      DGFunctor.id (QuotientObject C S) := by
  apply (universalEquiv R C S (QuotientObject C S)).injective
  change restrictContractedFunctor R C S (extension R _) = _
  rw [restrict_extension]
  apply ContractedFunctor.ext R
  · change (DGFunctor.id C).comp (inclusion R C S) =
      (inclusion R C S).comp (DGFunctor.id _)
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [DGFunctor.comp, DGFunctor.id, EnrichedFunctor.comp_map,
      EnrichedFunctor.id_map, eqToHom_refl, Category.comp_id, Category.id_comp]
  · exact heq_of_eq (funext (fun _ => rfl))

variable (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)
  (S : Set C) (T : Set D) (hF : ∀ x ∈ S, F.obj x ∈ T)

/-- 元の全 Hom 鎖写像は、同じ商包含の下で厳密に回収される。 -/
lemma quotientDGFunctor_original (x y : C) :
    (inclusion R C S).map x y ≫
        (quotientDGFunctor R C D F S T hF).map ⟨x⟩ ⟨y⟩ =
      F.map x y ≫ (inclusion R D T).map (F.obj x) (F.obj y) :=
  quotientEvaluation_original R (functorContracted R C D F S T hF) x y

variable (E : Type t) [DGCategory R E] [Small.{u} E] (G : DGFunctor R D E)
  (U : Set E) (hG : ∀ x ∈ T, G.obj x ∈ U)

/-- 正本商関手は同じ標準 ε を保つ関手の元の合成を厳密に保つ。 -/
lemma quotientDGFunctor_comp :
    quotientDGFunctor R C E (F.comp G) S U (fun x hx => hG _ (hF x hx)) =
      (quotientDGFunctor R C D F S T hF).comp (quotientDGFunctor R D E G T U hG) := by
  let qF := quotientDGFunctor R C D F S T hF
  let qG := quotientDGFunctor R D E G T U hG
  apply (universalEquiv R C S (QuotientObject E U)).injective
  change restrictContractedFunctor R C S (extension R _) =
    restrictContractedFunctor R C S (qF.comp qG)
  rw [restrict_extension, restrictContractedFunctor_comp]
  have hqF : restrictContractedFunctor R C S qF = functorContracted R C D F S T hF :=
    restrict_extension R _
  rw [hqF]
  apply ContractedFunctor.ext R
  · change (F.comp G).comp (inclusion R E U) = (F.comp (inclusion R D T)).comp qG
    have h := quotientDGFunctor_inclusion R D E G T U hG
    calc
      (F.comp G).comp (inclusion R E U) = F.comp (G.comp (inclusion R E U)) := functorAssoc _ _ _
      _ = F.comp ((inclusion R D T).comp qG) := congrArg (F.comp) h.symm
      _ = (F.comp (inclusion R D T)).comp qG := (functorAssoc _ _ _).symm
  · apply heq_of_eq
    funext b
    exact (quotientDGFunctor_epsilon R D E G T U hG ⟨F.obj b.val, hF b.val b.property⟩).symm

end SerrePositivity.DifferentialGraded.DGQuotient

end FunctorLaws
