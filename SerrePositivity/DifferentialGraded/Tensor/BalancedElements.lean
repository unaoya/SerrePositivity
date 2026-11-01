module

public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Module.LeftRepresentable
public import SerrePositivity.DifferentialGraded.Module.Yoneda
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import SerrePositivity.DifferentialGraded.Module.LeftHomElements
public import SerrePositivity.DifferentialGraded.Functor.Opposite
public import SerrePositivity.DifferentialGraded.Module.RestrictionAction
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.CurryingNaturality
public import SerrePositivity.DifferentialGraded.Module.LeftActionComparison
public import SerrePositivity.DifferentialGraded.Module.LeftEquivalence

/-!
# Tensor.BalancedElements

## 概要
20 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## LeftYoneda（旧 SerrePositivity/DifferentialGraded/Tensor/LeftYoneda.lean） -/

/-! # 左representableとbalanced tensorの評価 -/

@[expose] public section LeftYoneda
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右加群の作用は左representableに対するbalanced族を与える。 -/
def leftYonedaFamily (z : D) (M : RightModule A D) :
    BalancedFamily A D M (leftRepresentable A z) (M.obj (op z)) := by
  refine ⟨fun x => rightAction A D M z x, ?_⟩
  intro x y
  apply triple_ext
  intro a p b n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro m f h
  change GradedHom A z x b at h
  let la : (x ⟶[Complex A] y) ⊗ (z ⟶[Complex A] x) ⟶ (z ⟶[Complex A] y) :=
    leftAction A D (leftRepresentable A z) x y
  have hl := leftAction_apply A D (leftRepresentable A z) x y p b (p + b) rfl f h
  change la.f (p + b)
    (ιTensorObj (x ⟶[Complex A] y) (z ⟶[Complex A] x) p b (p + b) rfl (f ⊗ₜ[A] h)) = _ at hl
  change (rightAction A D M z x).f n
    ((rightAction A D M x y ▷ (z ⟶[Complex A] x)).f n
      (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (z ⟶[Complex A] x)
        (a + p) b n hn
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] h))) =
    (rightAction A D M z y).f n
      ((M.obj (op y) ◁ la).f n
        ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (z ⟶[Complex A] x)).hom.f n
          (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (z ⟶[Complex A] x)
            (a + p) b n hn
            (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) a p (a + p) rfl
              (m ⊗ₜ[A] f) ⊗ₜ[A] h))))
  rw [whiskerRight_apply, rightAction_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, hl, leftRepresentable_action]
  rw [rightAction_apply]
  have hs : moduleAction A M h ((a * p).negOnePow • moduleAction A M f m rfl) hn =
      (a * p).negOnePow • moduleAction A M h (moduleAction A M f m rfl) hn := by
    simp only [moduleAction, Units.smul_def, map_zsmul]
  rw [hs]
  have ht : moduleAction A M (x := op y) (y := op z)
      ((p * b).negOnePow • forward A (D := D) (x := z) (y := x) (z := y) h f
        (show b + p = p + b by omega)) m
      (show a + (p + b) = n by omega) =
    (p * b).negOnePow • moduleAction A M (x := op y) (y := op z)
      (forward A (D := D) (x := z) (y := x) (z := y) h f
        (show b + p = p + b by omega)) m (by omega) := by
    simp only [moduleAction, Units.smul_def, map_zsmul]
    rfl
  rw [ht]
  have hc := moduleAction_representable A y M (op x) (op z) b p a (p + b) n (a + p)
    rfl rfl (by omega) h f m
  change moduleAction A M (x := op y) (y := op z)
    (forward A (D := D) (x := z) (y := x) (z := y) h f (by omega)) m (by omega) = _ at hc
  rw [hc]
  simp only [smul_smul, ← Int.negOnePow_add]
  congr 1
  congr 1
  ring

/-- 左representableとのtensorから右加群の評価への射。 -/
def leftYonedaEvaluation (z : D) (M : RightModule A D) :
    obj A D M (leftRepresentable A z) ⟶ M.obj (op z) :=
  desc A D M (leftRepresentable A z) (leftYonedaFamily A D z M)

@[reassoc (attr := simp)]
lemma ι_leftYonedaEvaluation (z : D) (M : RightModule A D) (x : D) :
    ι A D M (leftRepresentable A z) x ≫ leftYonedaEvaluation A D z M =
      rightAction A D M z x :=
  ι_desc A D M (leftRepresentable A z) (leftYonedaFamily A D z M) x

lemma leftYonedaEvaluation_element (z : D) (M : RightModule A D) (x : D)
    {a p n : ℤ} (m : (M.obj (op x)).X a) (f : GradedHom A z x p) (hn : a + p = n) :
    (leftYonedaEvaluation A D z M).f n (element A D M (leftRepresentable A z) x m f hn) =
      (a * p).negOnePow • moduleAction A M f m hn := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p n hn (m ⊗ₜ[A] f)))
    (ι_leftYonedaEvaluation A D z M x)
  exact h.trans (rightAction_apply A D M z x a p n hn m f)

/-- 右側に単位Homを挿入する逆向きの射。 -/
def leftYonedaInsertion (z : D) (M : RightModule A D) :
    M.obj (op z) ⟶ obj A D M (leftRepresentable A z) :=
  freeUnitInsert A z (M.obj (op z)) ≫ ι A D M (leftRepresentable A z) z

lemma leftYonedaInsertion_apply (z : D) (M : RightModule A D) (a : ℤ)
    (m : (M.obj (op z)).X a) :
    (leftYonedaInsertion A D z M).f a m =
      element A D M (leftRepresentable A z) z m (unitElement A z).val (add_zero a) := by
  change (ι A D M (leftRepresentable A z) z).f a
    ((freeUnitInsert A z (M.obj (op z))).f a m) = _
  rw [freeUnitInsert_apply]
  rfl

@[reassoc (attr := simp)]
lemma leftYonedaInsertion_evaluation (z : D) (M : RightModule A D) :
    leftYonedaInsertion A D z M ≫ leftYonedaEvaluation A D z M = 𝟙 (M.obj (op z)) := by
  apply HomologicalComplex.hom_ext
  intro a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (leftYonedaEvaluation A D z M).f a ((leftYonedaInsertion A D z M).f a m) = m
  rw [leftYonedaInsertion_apply, leftYonedaEvaluation_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op z) a m

@[reassoc (attr := simp)]
lemma leftYonedaEvaluation_insertion (z : D) (M : RightModule A D) :
    leftYonedaEvaluation A D z M ≫ leftYonedaInsertion A D z M = 𝟙 _ := by
  apply hom_ext
  intro x
  apply tensorHom_ext
  intro a p n hn
  subst n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m f
  change (leftYonedaInsertion A D z M).f (a + p)
    ((leftYonedaEvaluation A D z M).f (a + p)
      (element A D M (leftRepresentable A z) x m f rfl)) =
    element A D M (leftRepresentable A z) x m f rfl
  rw [leftYonedaEvaluation_element]
  simp only [Units.smul_def, map_zsmul]
  rw [leftYonedaInsertion_apply]
  let la : (z ⟶[Complex A] x) ⊗ (z ⟶[Complex A] z) ⟶ (z ⟶[Complex A] x) :=
    leftAction A D (leftRepresentable A z) z x
  have hl := leftAction_apply A D (leftRepresentable A z) z x p 0 p (add_zero p)
    f (unitElement A z).val
  change la.f p (ιTensorObj (z ⟶[Complex A] x) (z ⟶[Complex A] z) p 0 p
    (add_zero p) (f ⊗ₜ[A] (unitElement A z).val)) = _ at hl
  have h := congrArg (fun k => k.f (a + p)
    (ιTensorObj (M.obj (op x) ⊗ (z ⟶[Complex A] x)) (z ⟶[Complex A] z)
      (a + p) 0 (a + p) (add_zero _)
      (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p (a + p) rfl
        (m ⊗ₜ[A] f) ⊗ₜ[A] (unitElement A z).val)))
    (condition A D M (leftRepresentable A z) z x)
  change (ι A D M (leftRepresentable A z) z).f (a + p)
    ((rightAction A D M z x ▷ (z ⟶[Complex A] z)).f (a + p)
      (ιTensorObj (M.obj (op x) ⊗ (z ⟶[Complex A] x)) (z ⟶[Complex A] z)
        (a + p) 0 (a + p) (add_zero _)
        (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p (a + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] (unitElement A z).val))) =
    (ι A D M (leftRepresentable A z) x).f (a + p)
      ((M.obj (op x) ◁ la).f (a + p)
        ((α_ (M.obj (op x)) (z ⟶[Complex A] x) (z ⟶[Complex A] z)).hom.f (a + p)
          (ιTensorObj (M.obj (op x) ⊗ (z ⟶[Complex A] x)) (z ⟶[Complex A] z)
            (a + p) 0 (a + p) (add_zero _)
            (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p (a + p) rfl
              (m ⊗ₜ[A] f) ⊗ₜ[A] (unitElement A z).val)))) at h
  rw [whiskerRight_apply, rightAction_apply,
    associator_apply_of_sums _ _ _ a p 0 (a + p) p (a + p) rfl (add_zero p),
    whiskerLeft_apply, hl, leftRepresentable_action] at h
  change ((a * p).negOnePow : ℤ) •
    (ι A D M (leftRepresentable A z) z).f (a + p)
      (ιTensorObj (M.obj (op z)) (z ⟶[Complex A] z) (a + p) 0 (a + p) (add_zero _)
        (moduleAction A M f m rfl ⊗ₜ[A] (unitElement A z).val)) =
    (ι A D M (leftRepresentable A z) x).f (a + p)
      (ιTensorObj (M.obj (op x)) (z ⟶[Complex A] x) a p (a + p) rfl (m ⊗ₜ[A] f))
  simpa only [mul_zero, Int.negOnePow_zero, one_smul, forward_unit,
    Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using h

/-- 左representableとのbalanced tensorも評価複体に同型。 -/
def leftYonedaIso (z : D) (M : RightModule A D) :
    obj A D M (leftRepresentable A z) ≅ M.obj (op z) where
  hom := leftYonedaEvaluation A D z M
  inv := leftYonedaInsertion A D z M
  hom_inv_id := leftYonedaEvaluation_insertion A D z M
  inv_hom_id := leftYonedaInsertion_evaluation A D z M

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end LeftYoneda

/-! ## LeftUnitSigns（旧 SerrePositivity/DifferentialGraded/Tensor/LeftUnitSigns.lean） -/

/-! # 左単位比較に現れる作用のKoszul符号 -/

@[expose] public section LeftUnitSigns
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B]

/-- 左因子を越える符号と左Yoneda評価の符号が作用の結合則と整合する。 -/
lemma moduleAction_signed_representable (M : RightModule A B) (b b' x : B)
    (p r s a n : ℤ) (ha : r + s = a) (hn : a + p = n)
    (f : GradedHom A (op b) (op b') p) (h : GradedHom A b x s)
    (m : (M.obj (op x)).X r) :
    (p * r).negOnePow • ((r * (p + s)).negOnePow •
      moduleAction A M (x := op x) (y := op b')
        (forward A (D := B) (x := b') (y := b) (z := x) (n := p + s) f h (by omega)) m (by omega)) =
    (r * s).negOnePow • moduleAction A M f (moduleAction A M h m ha) hn := by
  have hc := moduleAction_representable A x M (op b) (op b') p s r (p + s) n a
    (by omega) ha (by omega) f h m
  change moduleAction A M (x := op x) (y := op b')
    (forward A (D := B) (x := b') (y := b) (z := x) (n := p + s) f h (by omega)) m (by omega) =
      _ at hc
  rw [hc]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : p * r + r * (p + s) = r * s + 2 * (p * r) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

end SerrePositivity.DifferentialGraded
end

end LeftUnitSigns

/-! ## ChangeLeft（旧 SerrePositivity/DifferentialGraded/Tensor/ChangeLeft.lean） -/

/-! # 等しい左加群によるbalanced tensorの対象表示の変更 -/

@[expose] public section ChangeLeft
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群の等式でbalanced tensorを運ぶ標準同型。 -/
def changeLeft (M : RightModule A D) {N N' : LeftModule A D} (h : N = N') :
    obj A D M N ≅ obj A D M N' := eqToIso (congrArg (obj A D M) h)

@[reassoc]
lemma ι_changeLeft_hom (M : RightModule A D) {N N' : LeftModule A D} (h : N = N') (x : D) :
    ι A D M N x ≫ (changeLeft A D M h).hom =
      eqToHom (congrArg (fun L : LeftModule A D => M.obj (op x) ⊗ L.obj x) h) ≫ ι A D M N' x := by
  subst N'
  simp only [changeLeft, eqToIso_refl, Iso.refl_hom, Category.comp_id, eqToHom_refl,
    Category.id_comp]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ChangeLeft

/-! ## ElementsExt（旧 SerrePositivity/DifferentialGraded/Tensor/ElementsExt.lean） -/

/-! # balanced tensorを源とする全次数射の生成元による外延性 -/

@[expose] public section ElementsExt
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 微分と可換とは限らない斉次cochainも純粋生成元で判定できる。 -/
lemma cochain_element_ext {T : Complex A} {q : ℤ} (f g : Cochain (obj A D M N) T q)
    (h : ∀ (x : D) (r s a n : ℤ) (ha : r + s = a) (hn : a + q = n)
      (m : (M.obj (op x)).X r) (v : (N.obj x).X s),
      f.v a n hn (element A D M N x m v ha) =
        g.v a n hn (element A D M N x m v ha)) : f = g := by
  let : Epi (projection A D M N) := by
    dsimp [projection]
    infer_instance
  apply Cochain.ext
  intro a n hn
  apply (cancel_epi ((projection A D M N).f a)).mp
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) a)
    (colimit.isColimit (Discrete.functor (objectFamily A D M N)))).hom_ext
  intro x
  change (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ f.v a n hn =
    (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ g.v a n hn
  apply mapBifunctor.hom_ext
  intro r s ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m v
  exact h x.as r s a n ha hn m v

/-- 次数零の場合は同じ入出力次数で判定できる。 -/
lemma cochain_zero_element_ext {T : Complex A} (f g : Cochain (obj A D M N) T 0)
    (h : ∀ (x : D) (r s a : ℤ) (ha : r + s = a)
      (m : (M.obj (op x)).X r) (v : (N.obj x).X s),
      f.v a a (add_zero a) (element A D M N x m v ha) =
        g.v a a (add_zero a) (element A D M N x m v ha)) : f = g := by
  let : Epi (projection A D M N) := by
    dsimp [projection]
    infer_instance
  apply Cochain.ext₀
  intro a
  apply (cancel_epi ((projection A D M N).f a)).mp
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) a)
    (colimit.isColimit (Discrete.functor (objectFamily A D M N)))).hom_ext
  intro x
  change (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫
      f.v a a (add_zero a) =
    (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ g.v a a (add_zero a)
  apply mapBifunctor.hom_ext
  intro r s ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m v
  exact h x.as r s a ha m v

/-- 主Homへのchain mapも各包含への前合成で判定できる。 -/
lemma homMap_ext {K T : Complex A} (f g : K ⟶ homComplex A (obj A D M N) T)
    (h : ∀ x, f ≫ homPrecompose (ι A D M N x) T =
      g ≫ homPrecompose (ι A D M N x) T) : f = g := by
  apply (tensorRightHomEquiv (obj A D M N) K T).symm.injective
  apply param_hom_ext
  intro x
  apply (tensorRightHomEquiv (objectFamily A D M N x) K T).injective
  change curryRight ((𝟙 K ⊗ₘ ι A D M N x) ≫ uncurryRight f) =
    curryRight ((𝟙 K ⊗ₘ ι A D M N x) ≫ uncurryRight g)
  rw [curryRight_naturality_domain, curryRight_naturality_domain,
    curryRight_uncurryRight, curryRight_uncurryRight]
  exact h x

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ElementsExt

/-! ## ElementMap（旧 SerrePositivity/DifferentialGraded/Tensor/ElementMap.lean） -/

/-! # 包含で指定した射の純粋斉次元への評価 -/

@[expose] public section ElementMap
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma element_postcompose (M : RightModule A D) (N : LeftModule A D) (x : D)
    {T : Complex A} (f : obj A D M N ⟶ T) (g : objectFamily A D M N x ⟶ T)
    (h : ι A D M N x ≫ f = g) {r s n : ℤ}
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s = n) :
    f.f n (element A D M N x m v hn) =
      g.f n (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] v)) :=
  congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] v))) h

/-- 主Hom自然性の等式を純粋生成元での前後合成へ帰着する。 -/
lemma homMap_post_pre_eq (M : RightModule A D) (N : LeftModule A D)
    {K P Q T : Complex A} (F : K ⟶ homComplex A (obj A D M N) P)
    (G : K ⟶ homComplex A Q T) (f : P ⟶ T) (g : obj A D M N ⟶ Q)
    (h : ∀ (k : ℤ) (t : K.X k) (x : D) (r s a n : ℤ) (ha : r + s = a) (hn : a + k = n)
      (m : (M.obj (op x)).X r) (v : (N.obj x).X s),
      f.f n (((F.f k t).v a n hn) (element A D M N x m v ha)) =
      (G.f k t).v a n hn (g.f a (element A D M N x m v ha))) :
    F ≫ homPostcompose (obj A D M N) f = G ≫ homPrecompose g T := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (homPostcompose _ f).f k (F.f k t) = (homPrecompose g _).f k (G.f k t)
  rw [homPostcompose_apply, homPrecompose_apply]
  apply cochain_element_ext A D M N
  intro x r s a n ha hn m v
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.ofHom_v]
  exact h k t x r s a n ha hn m v

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ElementMap

/-! ## HomElements（旧 SerrePositivity/DifferentialGraded/Tensor/HomElements.lean） -/

/-! # balanced tensorの左右主Hom写像の全次数成分 -/

@[expose] public section HomElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma rightHomMap_element {M M' : RightModule A D} (N : LeftModule A D)
    {k r s n : ℤ} (τ : (moduleHom A D M M').X k) (x : D)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s + k = n) :
    (((rightHomMap A D M M' N).f k τ).v (r + s) n hn)
      (element A D M N x m v rfl) =
    element A D M' N x (((moduleHomπ A D M M' x).f k τ).v r (k + r) (by omega) m) v
      (by omega) := by
  change (curryComponent (rightParamMap A D N (fun y => moduleHomπ A D M M' y.unop)
    (moduleHomπ_naturality A D M M')) k τ).v (r + s) n hn _ = _
  rw [curryComponent_apply]
  exact rightParamMap_element A D N (fun y => moduleHomπ A D M M' y.unop)
    (moduleHomπ_naturality A D M M') x τ m v (by omega)

lemma leftHomMap_element (M : RightModule A D) {N N' : LeftModule A D}
    {k r s n : ℤ} (τ : (leftModuleHom A D N N').X k) (x : D)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s + k = n) :
    (((leftHomMap A D M N N').f k τ).v (r + s) n hn)
      (element A D M N x m v rfl) =
    (k * r).negOnePow • element A D M N' x m
      (((leftModuleHomπ A D N N' x).f k τ).v s (k + s) (by omega) v) (by omega) := by
  change (curryComponent (leftParamMap A D M (leftModuleHomπ A D N N')
    (leftModuleHomπ_naturality A D N N')) k τ).v (r + s) n hn _ = _
  rw [curryComponent_apply]
  exact leftParamMap_element A D M (leftModuleHomπ A D N N')
    (leftModuleHomπ_naturality A D N N') x τ m v (by omega)

lemma rightHomMap_element_of_sum {M M' : RightModule A D} (N : LeftModule A D)
    {k r s a l n : ℤ} (τ : (moduleHom A D M M').X k) (x : D)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s)
    (ha : r + s = a) (hl : k + r = l) (hn : a + k = n) :
    (((rightHomMap A D M M' N).f k τ).v a n hn) (element A D M N x m v ha) =
    element A D M' N x (((moduleHomπ A D M M' x).f k τ).v r l (by omega) m) v
      (by omega) := by
  subst a l
  exact rightHomMap_element A D N τ x m v hn

lemma leftHomMap_element_of_sum (M : RightModule A D) {N N' : LeftModule A D}
    {k r s a l n : ℤ} (τ : (leftModuleHom A D N N').X k) (x : D)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s)
    (ha : r + s = a) (hl : k + s = l) (hn : a + k = n) :
    (((leftHomMap A D M N N').f k τ).v a n hn) (element A D M N x m v ha) =
    (k * r).negOnePow • element A D M N' x m
      (((leftModuleHomπ A D N N' x).f k τ).v s l (by omega) v) (by omega) := by
  subst a l
  exact leftHomMap_element A D M τ x m v hn

lemma element_units_smul_right (M : RightModule A D) (N : LeftModule A D) (x : D)
    {r s n : ℤ} (u : ℤˣ) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (hn : r + s = n) :
    element A D M N x m (u • v) hn = u • element A D M N x m v hn := by
  have ht : m ⊗ₜ[A] (u • v) = u • (m ⊗ₜ[A] v) :=
    map_zsmul (TensorProduct.mk A _ _ m) (u : ℤ) v
  unfold element
  rw [ht]
  simp only [Units.smul_def, map_zsmul]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end HomElements

/-! ## RightParameter（旧 SerrePositivity/DifferentialGraded/Tensor/RightParameter.lean） -/

/-! # 右に置いたパラメータ複体とbalanced tensorの普遍性 -/

@[expose] public section RightParameter
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 各対象のtensorの右にKを置き、二作用の後の▷Kでbalanced条件を課す。 -/
def RightParamFamily (K T : Complex A) :=
  { a : ∀ x : D, objectFamily A D M N x ⊗ K ⟶ T // ∀ x y : D,
    ((rightAction A D M x y ▷ N.obj x) ▷ K) ≫ a x =
      (((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y) ▷ K) ≫ a y }

/-- 右tensor転置により、右パラメータ族をHom(K,T)値のbalanced族にする。 -/
def curryRightParamFamily {K T : Complex A} (a : RightParamFamily A D M N K T) :
    BalancedFamily A D M N (homComplex A K T) := by
  refine ⟨fun x => curryRight (a.val x), ?_⟩
  intro x y
  have h := congrArg curryRight (a.property x y)
  change curryRight (((rightAction A D M x y ▷ N.obj x) ⊗ₘ 𝟙 K) ≫ a.val x) =
    curryRight ((((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
      M.obj (op y) ◁ leftAction A D N x y) ⊗ₘ 𝟙 K) ≫ a.val y) at h
  rw [curryRight_naturality_source, curryRight_naturality_source] at h
  exact h

variable [Small.{u} D]

/-- 右パラメータを持つbalanced族を(M⊗_D N)⊗Kへ降ろす。 -/
def rightParamDesc {K T : Complex A} (a : RightParamFamily A D M N K T) :
    obj A D M N ⊗ K ⟶ T :=
  uncurryRight (desc A D M N (curryRightParamFamily A D M N a))

@[reassoc (attr := simp)]
lemma ι_rightParamDesc {K T : Complex A} (a : RightParamFamily A D M N K T) (x : D) :
    (ι A D M N x ▷ K) ≫ rightParamDesc A D M N a = a.val x := by
  apply (tensorRightHomEquiv K _ T).injective
  change curryRight ((ι A D M N x ⊗ₘ 𝟙 K) ≫
    uncurryRight (desc A D M N (curryRightParamFamily A D M N a))) = curryRight (a.val x)
  rw [curryRight_naturality_source, curryRight_uncurryRight, ι_desc]
  rfl

lemma rightParam_hom_ext {K T : Complex A} (f g : obj A D M N ⊗ K ⟶ T)
    (h : ∀ x, (ι A D M N x ▷ K) ≫ f = (ι A D M N x ▷ K) ≫ g) : f = g := by
  apply (tensorRightHomEquiv K _ T).injective
  apply hom_ext A D M N
  intro x
  have hx := congrArg curryRight (h x)
  change curryRight ((ι A D M N x ⊗ₘ 𝟙 K) ≫ f) =
    curryRight ((ι A D M N x ⊗ₘ 𝟙 K) ≫ g) at hx
  rw [curryRight_naturality_source, curryRight_naturality_source] at hx
  exact hx

/-- 射を右パラメータ付きの対象ごとの族へ制限する。 -/
def rightParamRestrict {K T : Complex A} (f : obj A D M N ⊗ K ⟶ T) :
    RightParamFamily A D M N K T := by
  refine ⟨fun x => (ι A D M N x ▷ K) ≫ f, ?_⟩
  intro x y
  have h := congrArg (fun t => (t ▷ K) ≫ f) (condition A D M N x y)
  simpa only [comp_whiskerRight, Category.assoc] using h

/-- 右パラメータ付きbalanced tensorの普遍性。 -/
def rightParamHomEquiv (K T : Complex A) :
    (obj A D M N ⊗ K ⟶ T) ≃ RightParamFamily A D M N K T where
  toFun := rightParamRestrict A D M N
  invFun := rightParamDesc A D M N
  left_inv f := by
    apply rightParam_hom_ext A D M N
    intro x
    exact ι_rightParamDesc A D M N (rightParamRestrict A D M N f) x
  right_inv a := by
    apply Subtype.ext
    funext x
    exact ι_rightParamDesc A D M N a x

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end RightParameter

/-! ## ModuleParameter（旧 SerrePositivity/DifferentialGraded/Tensor/ModuleParameter.lean） -/

/-! # パラメータ複体と右加群のbalanced作用の整合性 -/

@[expose] public section ModuleParameter
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 右balanced作用ではパラメータを横切る二つのKoszul符号が消える。 -/
lemma rightAction_tensorModule (K : Complex A) (M : RightModule A D) (x y : D) :
    rightAction A D (tensorModule K M) x y =
      (α_ K (M.obj (op y)) (x ⟶[Complex A] y)).hom ≫ K ◁ rightAction A D M x y := by
  apply triple_ext
  intro k r p n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro t m f
  change (rightAction A D (tensorModule K M) x y).f n
    (ιTensorObj (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (k + r) p n hn
      (ιTensorObj K (M.obj (op y)) k r (k + r) rfl (t ⊗ₜ[A] m) ⊗ₜ[A] f)) =
    (K ◁ rightAction A D M x y).f n
      ((α_ K (M.obj (op y)) (x ⟶[Complex A] y)).hom.f n
        (ιTensorObj (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (k + r) p n hn
          (ιTensorObj K (M.obj (op y)) k r (k + r) rfl (t ⊗ₜ[A] m) ⊗ₜ[A] f)))
  rw [rightAction_apply, tensorModule_action K M (op y) (op x) p k r (k + r)
    (r + p) n rfl rfl hn, associator_apply, whiskerLeft_apply, rightAction_apply]
  have ht : t ⊗ₜ[A] ((r * p).negOnePow • moduleAction A M f m rfl) =
      (r * p).negOnePow • (t ⊗ₜ[A] moduleAction A M f m rfl) :=
    map_zsmul (TensorProduct.mk A _ _ t) ((r * p).negOnePow : ℤ) _
  rw [ht]
  simp only [Units.smul_def, map_zsmul]
  change ((k + r) * p).negOnePow • ((p * k).negOnePow •
      ιTensorObj K (M.obj (op x)) k (r + p) n (by omega)
        (t ⊗ₜ[A] moduleAction A M f m rfl)) =
    (r * p).negOnePow • ιTensorObj K (M.obj (op x)) k (r + p) n (by omega)
      (t ⊗ₜ[A] moduleAction A M f m rfl)
  rw [smul_smul, ← Int.negOnePow_add]
  have hs : (k + r) * p + p * k = r * p + 2 * (p * k) := by ring
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ModuleParameter

/-! ## YonedaNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/YonedaNaturality.lean） -/

/-! # balanced tensorのYoneda評価の自然性 -/

@[expose] public section YonedaNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

@[reassoc]
lemma yonedaEvaluation_naturality (z : D) {N N' : LeftModuleCategory A D} (g : N ⟶ N') :
    map A D (𝟙 (ForgetEnrichment.of (Complex A) (representable A z))) g ≫
      yonedaEvaluation A D z (ForgetEnrichment.to (Complex A) N') =
    yonedaEvaluation A D z (ForgetEnrichment.to (Complex A) N) ≫
      (leftModuleEvaluation A D z).map g := by
  apply hom_ext
  intro x
  simp only [ι_map_assoc, CategoryTheory.Functor.map_id]
  change (𝟙 (x ⟶[Complex A] z) ⊗ₘ (leftModuleEvaluation A D x).map g) ≫
      ι A D (representable A z) (ForgetEnrichment.to (Complex A) N') x ≫
        yonedaEvaluation A D z (ForgetEnrichment.to (Complex A) N') =
    ι A D (representable A z) (ForgetEnrichment.to (Complex A) N) x ≫
      yonedaEvaluation A D z (ForgetEnrichment.to (Complex A) N) ≫
        (leftModuleEvaluation A D z).map g
  rw [ι_yonedaEvaluation, ι_yonedaEvaluation_assoc]
  exact (leftAction_morphism A D g x z).symm

@[reassoc]
lemma leftYonedaEvaluation_naturality (z : D) {M M' : ModuleCategory A D} (f : M ⟶ M') :
    map A D f (𝟙 (ForgetEnrichment.of (Complex A) (leftRepresentable A z))) ≫
      leftYonedaEvaluation A D z (ForgetEnrichment.to (Complex A) M') =
    leftYonedaEvaluation A D z (ForgetEnrichment.to (Complex A) M) ≫
      (moduleEvaluation A D z).map f := by
  apply hom_ext
  intro x
  simp only [ι_map_assoc, CategoryTheory.Functor.map_id]
  change ((moduleEvaluation A D x).map f ⊗ₘ 𝟙 (z ⟶[Complex A] x)) ≫
      ι A D (ForgetEnrichment.to (Complex A) M') (leftRepresentable A z) x ≫
        leftYonedaEvaluation A D z (ForgetEnrichment.to (Complex A) M') =
    ι A D (ForgetEnrichment.to (Complex A) M) (leftRepresentable A z) x ≫
      leftYonedaEvaluation A D z (ForgetEnrichment.to (Complex A) M) ≫
        (moduleEvaluation A D z).map f
  rw [ι_leftYonedaEvaluation, ι_leftYonedaEvaluation_assoc]
  exact (rightAction_morphism A D f z x).symm

/-- 左加群の任意次数のHomに対するYoneda評価の生成元上の自然性。 -/
lemma yonedaEvaluation_homElement {N N' : LeftModule A D} {q p r n k l : ℤ}
    (τ : (leftModuleHom A D N N').X q) (z x : D)
    (f : GradedHom A x z p) (m : (N.obj x).X r)
    (hn : p + r = n) (hk : r + q = k) (hl : n + q = l) :
    (((leftModuleHomπ A D N N' z).f q τ).v n l hl)
      ((yonedaEvaluation A D z N).f n (element A D (representable A z) N x f m hn)) =
    (q * p).negOnePow • (yonedaEvaluation A D z N').f l
      (element A D (representable A z) N' x f
        ((((leftModuleHomπ A D N N' x).f q τ).v r k hk) m) (by omega)) := by
  rw [yonedaEvaluation_element, yonedaEvaluation_element]
  exact leftModuleHomElement_action A D τ x z f m (by omega) hk hl

/-- 右加群の任意次数のHomに対する反対側の評価の生成元上の自然性。 -/
lemma leftYonedaEvaluation_homElement {M M' : RightModule A D} {q p r n k l : ℤ}
    (τ : (moduleHom A D M M').X q) (z x : D)
    (m : (M.obj (op x)).X r) (f : GradedHom A z x p)
    (hn : r + p = n) (hk : r + q = k) (hl : n + q = l) :
    (((moduleHomπ A D M M' z).f q τ).v n l hl)
      ((leftYonedaEvaluation A D z M).f n
        (element A D M (leftRepresentable A z) x m f hn)) =
    (leftYonedaEvaluation A D z M').f l
      (element A D M' (leftRepresentable A z) x
        ((((moduleHomπ A D M M' x).f q τ).v r k hk) m) f (by omega)) := by
  have h := Cochain.congr_v (moduleHomElement_naturality A D q τ (op x) (op z) p f)
    r l (by omega)
  rw [Cochain.comp_v _ _ _ r n l hn hl, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ r k l hk (by omega)] at h
  have he := congrArg (fun t => t m) h
  change (((moduleHomπ A D M M' z).f q τ).v n l hl) (moduleAction A M f m hn) =
    (q * p).negOnePow • moduleAction A M' f
      ((((moduleHomπ A D M M' x).f q τ).v r k hk) m) (by omega) at he
  rw [leftYonedaEvaluation_element, leftYonedaEvaluation_element]
  simp only [Units.smul_def, map_zsmul]
  change (r * p).negOnePow •
    ((((moduleHomπ A D M M' z).f q τ).v n l hl) (moduleAction A M f m hn)) =
    (k * p).negOnePow • moduleAction A M' f
      ((((moduleHomπ A D M M' x).f q τ).v r k hk) m) (by omega)
  rw [he]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : r * p + q * p = k * p := by
    rw [← hk]
    ring
  rw [hs]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end YonedaNaturality

/-! ## RestrictBalanced（旧 SerrePositivity/DifferentialGraded/Tensor/RestrictBalanced.lean） -/

/-! # dg関手に沿うbalanced族の引き戻し

## 概要
右作用のKoszul交換を保ち、任意次数の関係を元のdg圏の関係へ送る。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictBalanced
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] (F : DGFunctor A D E)

lemma rightAction_restrict (M : RightModule A E) (x y : D) :
    rightAction A D (restrictModule A D E F.op M) x y =
      (𝟙 (M.obj (op (F.obj y))) ⊗ₘ F.map x y) ≫ rightAction A E M (F.obj x) (F.obj y) := by
  change (signedSwap (M.obj (op (F.obj y))) (homObject A D x y)).hom ≫
    uncurryRight (F.map x y ≫ M.map (op (F.obj y)) (op (F.obj x))) =
      (𝟙 _ ⊗ₘ F.map x y) ≫
        (signedSwap (M.obj (op (F.obj y))) (homObject A E (F.obj x) (F.obj y))).hom ≫
          uncurryRight (M.map (op (F.obj y)) (op (F.obj x)))
  rw [uncurryRight_precompose]
  change (signedSwap _ _).hom ≫ (F.map x y ⊗ₘ 𝟙 _) ≫ _ = _
  rw [← Category.assoc, ← signedSwap_naturality, Category.assoc]

lemma leftAction_restrict (N : LeftModule A E) (x y : D) :
    leftAction A D (F.comp N) x y =
      (F.map x y ⊗ₘ 𝟙 (N.obj (F.obj x))) ≫ leftAction A E N (F.obj x) (F.obj y) := by
  change uncurryRight (F.map x y ≫ N.map (F.obj x) (F.obj y)) = _
  exact uncurryRight_precompose (F.map x y) (N.map (F.obj x) (F.obj y))

variable [Small.{u} D]

/-- target上のbalanced族を、両作用を制限したsource上のbalanced族へ引き戻す。 -/
def restrictFamily (M : RightModule A E) (N : LeftModule A E) {T : Complex A}
    (a : BalancedFamily A E M N T) :
    BalancedFamily A D (restrictModule A D E F.op M) (F.comp N) T := by
  refine ⟨fun x => a.val (F.obj x), ?_⟩
  intro x y
  rw [rightAction_restrict, comp_whiskerRight, Category.assoc]
  change ((𝟙 (M.obj (op (F.obj y))) ⊗ₘ F.map x y) ▷ N.obj (F.obj x)) ≫
      (rightAction A E M (F.obj x) (F.obj y) ▷ N.obj (F.obj x)) ≫ a.val (F.obj x) =
    (α_ (M.obj (op (F.obj y))) (x ⟶[Complex A] y) (N.obj (F.obj x))).hom ≫
      M.obj (op (F.obj y)) ◁ leftAction A D (F.comp N) x y ≫ a.val (F.obj y)
  rw [a.property, leftAction_restrict, whiskerLeft_comp]
  rw [tensorHom_def, id_whiskerRight, Category.id_comp, associator_naturality_middle_assoc]
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, Category.assoc]

@[reassoc] lemma ι_restrictFamily_desc (M : RightModule A E) (N : LeftModule A E)
    {T : Complex A} (a : BalancedFamily A E M N T) (x : D) :
    ι A D (restrictModule A D E F.op M) (F.comp N) x ≫
      desc A D _ _ (restrictFamily A D E F M N a) = a.val (F.obj x) :=
  ι_desc A D _ _ _ x

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end RestrictBalanced

/-! ## DegreeElementsExt（旧 SerrePositivity/DifferentialGraded/Tensor/DegreeElementsExt.lean） -/

/-! # balanced tensorの各次数からの線形射の外延性 -/

@[expose] public section DegreeElementsExt
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 出力次数や微分との可換性を仮定せず、固定次数の線形射を生成元で判定する。 -/
lemma degree_element_ext {a : ℤ} {V : ModuleCat.{u} A}
    (f g : (obj A D M N).X a ⟶ V)
    (h : ∀ (x : D) (r s : ℤ) (ha : r + s = a)
      (m : (M.obj (op x)).X r) (v : (N.obj x).X s),
      f (element A D M N x m v ha) = g (element A D M N x m v ha)) : f = g := by
  let : Epi (projection A D M N) := by
    dsimp [projection]
    infer_instance
  apply (cancel_epi ((projection A D M N).f a)).mp
  apply (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) a)
    (colimit.isColimit (Discrete.functor (objectFamily A D M N)))).hom_ext
  intro x
  change (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ f =
    (Sigma.ι (objectFamily A D M N) x.as).f a ≫ (projection A D M N).f a ≫ g
  apply mapBifunctor.hom_ext
  intro r s ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m v
  exact h x.as r s ha m v

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end DegreeElementsExt

/-! ## ParameterEvaluation（旧 SerrePositivity/DifferentialGraded/Tensor/ParameterEvaluation.lean） -/

/-! # 左右パラメータ付き降下の純粋生成元計算 -/

@[expose] public section ParameterEvaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

lemma paramDesc_element {K T : Complex A} (a : ParamFamily A D M N K T) (x : D)
    {k r s l n : ℤ} (hl : r + s = l) (hn : k + l = n)
    (t : K.X k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) :
    (paramDesc A D M N a).f n
      (ιTensorObj K (obj A D M N) k l n hn (t ⊗ₜ[A] element A D M N x m v hl)) =
    (a.val x).f n (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k l n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v))) := by
  have h := congrArg (fun f => f.f n
    (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k l n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v))))
    (ι_paramDesc A D M N a x)
  change (paramDesc A D M N a).f n ((K ◁ ι A D M N x).f n
    (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k l n hn
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v)))) = _ at h
  rw [whiskerLeft_apply] at h
  exact h

lemma rightParamDesc_element {K T : Complex A} (a : RightParamFamily A D M N K T) (x : D)
    {r s l k n : ℤ} (hl : r + s = l) (hn : l + k = n)
    (m : (M.obj (op x)).X r) (v : (N.obj x).X s) (t : K.X k) :
    (rightParamDesc A D M N a).f n
      (ιTensorObj (obj A D M N) K l k n hn (element A D M N x m v hl ⊗ₜ[A] t)) =
    (a.val x).f n (ιTensorObj (M.obj (op x) ⊗ N.obj x) K l k n hn
      (ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v) ⊗ₜ[A] t)) := by
  have h := congrArg (fun f => f.f n
    (ιTensorObj (M.obj (op x) ⊗ N.obj x) K l k n hn
      (ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v) ⊗ₜ[A] t)))
    (ι_rightParamDesc A D M N a x)
  change (rightParamDesc A D M N a).f n ((ι A D M N x ▷ K).f n
    (ιTensorObj (M.obj (op x) ⊗ N.obj x) K l k n hn
      (ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v) ⊗ₜ[A] t))) = _ at h
  rw [whiskerRight_apply] at h
  exact h

lemma paramDesc_curry_element {K T : Complex A} (a : ParamFamily A D M N K T) (x : D)
    {k r s l n : ℤ} (hl : r + s = l) (hn : l + k = n)
    (t : K.X k) (m : (M.obj (op x)).X r) (v : (N.obj x).X s) :
    ((curryRight (paramDesc A D M N a)).f k t).v l n hn (element A D M N x m v hl) =
    (a.val x).f n (ιTensorObj K (M.obj (op x) ⊗ N.obj x) k l n (by omega)
      (t ⊗ₜ[A] ιTensorObj (M.obj (op x)) (N.obj x) r s l hl (m ⊗ₜ[A] v))) := by
  exact paramDesc_element A D M N a x hl (by omega) t m v

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ParameterEvaluation

/-! ## ParameterTensorFamilies（旧 SerrePositivity/DifferentialGraded/Tensor/ParameterTensorFamilies.lean） -/

/-! # パラメータ付きbalanced族とtensor加群のbalanced族 -/

@[expose] public section ParameterTensorFamilies
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- associatorで族の表示を替えたときの二つのbalanced条件は同値。 -/
lemma parameter_balanced_condition_iff (K : Complex A) (M : RightModule A D)
    (N : LeftModule A D) {T : Complex A}
    (a : ∀ x, K ⊗ objectFamily A D M N x ⟶ T) (x y : D) :
    ((rightAction A D (tensorModule K M) x y ▷ N.obj x) ≫
        (α_ K (M.obj (op x)) (N.obj x)).hom ≫ a x =
      (α_ (K ⊗ M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        (K ⊗ M.obj (op y)) ◁ leftAction A D N x y ≫
          (α_ K (M.obj (op y)) (N.obj y)).hom ≫ a y) ↔
    ((K ◁ (rightAction A D M x y ▷ N.obj x)) ≫ a x =
      (K ◁ ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom ≫
        M.obj (op y) ◁ leftAction A D N x y)) ≫ a y) := by
  rw [rightAction_tensorModule, comp_whiskerRight, Category.assoc,
    associator_naturality_middle_assoc, associator_naturality_right_assoc, ← pentagon_assoc]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [cancel_epi, cancel_epi]

/-- Kを左に置くbalanced族を、tensor加群のbalanced族へ移す。 -/
def paramTensorFamily {M : RightModule A D} {N : LeftModule A D} {K T : Complex A}
    (a : ParamFamily A D M N K T) : BalancedFamily A D (tensorModule K M) N T := by
  refine ⟨fun x => (α_ K (M.obj (op x)) (N.obj x)).hom ≫ a.val x, ?_⟩
  intro x y
  exact (parameter_balanced_condition_iff A D K M N a.val x y).2 (a.property x y)

/-- tensor加群のbalanced族を、Kを左に置く族へ戻す。 -/
def tensorParamFamily {M : RightModule A D} {N : LeftModule A D} {K T : Complex A}
    (b : BalancedFamily A D (tensorModule K M) N T) : ParamFamily A D M N K T := by
  refine ⟨fun x => (α_ K (M.obj (op x)) (N.obj x)).inv ≫ b.val x, ?_⟩
  intro x y
  apply (parameter_balanced_condition_iff A D K M N _ x y).1
  simpa only [Iso.hom_inv_id_assoc] using b.property x y

/-- パラメータ複体を右加群のtensorへ移す族の同値。 -/
def paramTensorFamilyEquiv (K : Complex A) (M : RightModule A D) (N : LeftModule A D)
    (T : Complex A) : ParamFamily A D M N K T ≃ BalancedFamily A D (tensorModule K M) N T where
  toFun := paramTensorFamily A D
  invFun := tensorParamFamily A D
  left_inv a := by
    apply Subtype.ext
    funext x
    exact Iso.inv_hom_id_assoc (α_ K (M.obj (op x)) (N.obj x)) (a.val x)
  right_inv b := by
    apply Subtype.ext
    funext x
    exact Iso.hom_inv_id_assoc (α_ K (M.obj (op x)) (N.obj x)) (b.val x)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ParameterTensorFamilies

/-! ## TensorModuleIso（旧 SerrePositivity/DifferentialGraded/Tensor/TensorModuleIso.lean） -/

/-! # 生成複体とのtensorをbalanced tensorの外へ出す同型

## 概要
生成複体とのtensorをbalanced tensorの外へ出す同型。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/ModuleCylinderKFlat.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorModuleIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (K : Complex A) (M : RightModule A D) (N : LeftModule A D)

def tensorModuleHom : obj A D (tensorModule K M) N ⟶ K ⊗ obj A D M N :=
  desc A D (tensorModule K M) N
    (paramTensorFamily A D (paramRestrict A D M N (𝟙 (K ⊗ obj A D M N))))

def tensorModuleInv : K ⊗ obj A D M N ⟶ obj A D (tensorModule K M) N :=
  paramDesc A D M N (tensorParamFamily A D
    (homEquiv A D (tensorModule K M) N _ (𝟙 (obj A D (tensorModule K M) N))))

@[reassoc]
lemma ι_tensorModuleHom (x : D) :
    ι A D (tensorModule K M) N x ≫ tensorModuleHom A D K M N =
      (α_ K (M.obj (Opposite.op x)) (N.obj x)).hom ≫ K ◁ ι A D M N x := by
  rw [tensorModuleHom, ι_desc]
  change (α_ K (M.obj (Opposite.op x)) (N.obj x)).hom ≫
    ((K ◁ ι A D M N x) ≫ 𝟙 _) = _
  rw [Category.comp_id]

@[reassoc]
lemma ι_tensorModuleInv (x : D) :
    (K ◁ ι A D M N x) ≫ tensorModuleInv A D K M N =
      (α_ K (M.obj (Opposite.op x)) (N.obj x)).inv ≫ ι A D (tensorModule K M) N x := by
  rw [tensorModuleInv, ι_paramDesc]
  change (α_ K (M.obj (Opposite.op x)) (N.obj x)).inv ≫
    (ι A D (tensorModule K M) N x ≫ 𝟙 _) = _
  rw [Category.comp_id]

def tensorModuleIso : obj A D (tensorModule K M) N ≅ K ⊗ obj A D M N where
  hom := tensorModuleHom A D K M N
  inv := tensorModuleInv A D K M N
  hom_inv_id := by
    apply hom_ext A D (tensorModule K M) N
    intro x
    rw [ι_tensorModuleHom_assoc, ι_tensorModuleInv, Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply param_hom_ext A D M N
    intro x
    rw [ι_tensorModuleInv_assoc, ι_tensorModuleHom, Iso.inv_hom_id_assoc, Category.comp_id]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end TensorModuleIso

/-! ## BalancedUnitElements（旧 SerrePositivity/DifferentialGraded/Tensor/BalancedUnitElements.lean） -/

/-! # 右次数零のbalanced関係

## 概要
右次数零のbalanced関係。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BalancedUnitElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
lemma leftAction_heq (N : LeftModule A D) {x y : D} {p r n n' : ℤ}
    (f : GradedHom A x y p) (t : (N.obj x).X r)
    (hn : r + p = n) (hn' : r + p = n') :
    HEq (DifferentialGraded.leftAction A N f t hn)
      (DifferentialGraded.leftAction A N f t hn') := by
  have h : n = n' := hn.symm.trans hn'
  cases h
  rfl

lemma element_balanced_zero (M : RightModule A D) (N : LeftModule A D) (x y : D)
    {r p : ℤ} (m : (M.obj (op y)).X r) (f : GradedHom A x y p)
    (t : (N.obj x).X 0) :
    (r * p).negOnePow • element A D M N x (moduleAction A M f m rfl) t
      (add_zero (r + p)) =
    element A D M N y m
      (SerrePositivity.DifferentialGraded.leftAction A N f t (zero_add p)) rfl := by
  convert (element_balanced A D M N x y m f t (add_zero (r + p))) using 1
  congr 1
  · exact (add_zero p).symm
  · exact leftAction_heq A D N f t _ _
  · exact proof_irrel_heq _ _

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end BalancedUnitElements

/-! ## BalancedFamilyElements（旧 SerrePositivity/DifferentialGraded/Tensor/BalancedFamilyElements.lean） -/

/-! # balancedなchain map族の斉次生成元による判定 -/

@[expose] public section BalancedFamilyElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 各対象で与えられたtensor射を純粋斉次元に適用する。 -/
def familyElement {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T) (x : D) {r s n : ℤ}
    (m : (M.obj (op x)).X r) (t : (N.obj x).X s) (hn : r + s = n) : T.X n :=
  (a x).f n (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] t))

lemma balancedFamily_element {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : BalancedFamily A D M N T) (x y : D) {r p s n : ℤ}
    (m : (M.obj (op y)).X r) (f : GradedHom A x y p) (t : (N.obj x).X s)
    (hn : r + p + s = n) :
    (r * p).negOnePow • familyElement A D a.val x (moduleAction A M f m rfl) t hn =
    familyElement A D a.val y m
      (SerrePositivity.DifferentialGraded.leftAction A N
        (n := p + s) f t (by omega)) (by omega) := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
        (m ⊗ₜ[A] f) ⊗ₜ[A] t))) (a.property x y)
  change (a.val x).f n
    ((rightAction A D M x y ▷ N.obj x).f n
      (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (a.val y).f n ((M.obj (op y) ◁ leftAction A D N x y).f n
      ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom.f n
        (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
          (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
            (m ⊗ₜ[A] f) ⊗ₜ[A] t)))) at h
  rw [whiskerRight_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, leftAction_apply] at h
  simpa only [familyElement, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using h

/-- 純粋斉次生成元でのbalanced関係からchain map族のbalanced性を復元する。 -/
def balancedFamilyMk {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T)
    (h : ∀ (x y : D) (r p s n : ℤ) (hn : r + p + s = n)
      (m : (M.obj (op y)).X r) (f : GradedHom A x y p) (t : (N.obj x).X s),
      (r * p).negOnePow • familyElement A D a x (moduleAction A M f m rfl) t hn =
      familyElement A D a y m
        (SerrePositivity.DifferentialGraded.leftAction A N
        (n := p + s) f t (by omega)) (by omega)) :
    BalancedFamily A D M N T := by
  refine ⟨a, ?_⟩
  intro x y
  apply triple_ext
  intro r p s n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro m f t
  change (a x).f n
    ((rightAction A D M x y ▷ N.obj x).f n
      (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
        (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
          (m ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (a y).f n ((M.obj (op y) ◁ leftAction A D N x y).f n
      ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom.f n
        (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) (r + p) s n hn
          (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p (r + p) rfl
            (m ⊗ₜ[A] f) ⊗ₜ[A] t))))
  rw [whiskerRight_apply, rightAction_apply, associator_apply,
    whiskerLeft_apply, leftAction_apply]
  simpa only [familyElement, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using
    h x y r p s n hn m f t

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end BalancedFamilyElements

/-! ## BalancedReindex（旧 SerrePositivity/DifferentialGraded/Tensor/BalancedReindex.lean） -/

/-! # 中間次数を指定するbalanced族の生成元関係 -/

@[expose] public section BalancedReindex
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma balancedFamily_element_of_sums {M : RightModule A D} {N : LeftModule A D} {T : Complex A}
    (a : BalancedFamily A D M N T) (x y : D) {r p s i j n : ℤ}
    (hi : r + p = i) (hj : s + p = j) (hn : i + s = n)
    (m : (M.obj (op y)).X r) (f : GradedHom A x y p) (t : (N.obj x).X s) :
    (r * p).negOnePow • familyElement A D a.val x (moduleAction A M f m hi) t hn =
    familyElement A D a.val y m
      (SerrePositivity.DifferentialGraded.leftAction A N (n := j) f t hj) (by omega) := by
  have h := congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) i s n hn
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p i hi
        (m ⊗ₜ[A] f) ⊗ₜ[A] t))) (a.property x y)
  change (a.val x).f n ((rightAction A D M x y ▷ N.obj x).f n
    (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) i s n hn
      (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p i hi
        (m ⊗ₜ[A] f) ⊗ₜ[A] t))) =
    (a.val y).f n ((M.obj (op y) ◁ leftAction A D N x y).f n
      ((α_ (M.obj (op y)) (x ⟶[Complex A] y) (N.obj x)).hom.f n
        (ιTensorObj (M.obj (op y) ⊗ (x ⟶[Complex A] y)) (N.obj x) i s n hn
          (ιTensorObj (M.obj (op y)) (x ⟶[Complex A] y) r p i hi
            (m ⊗ₜ[A] f) ⊗ₜ[A] t)))) at h
  rw [whiskerRight_apply, rightAction_apply,
    associator_apply_of_sums _ _ _ r p s i j n hi (by omega) hn,
    whiskerLeft_apply, leftAction_apply] at h
  simpa only [familyElement, Units.smul_def, ← TensorProduct.smul_tmul', map_zsmul] using h

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end BalancedReindex

/-! ## SwapFamilies（旧 SerrePositivity/DifferentialGraded/Tensor/SwapFamilies.lean） -/

/-! # opposite上のbalanced族の符号付き交換 -/

@[expose] public section SwapFamilies
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- opposite側の族をsigned braidingで元のtensor順序へ戻す。 -/
def swapFamilyApp (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (b : ∀ x, objectFamily A Dᵒᵖ N.toRightOpposite M.toFunctor x ⟶ T) (x : D) :
    objectFamily A D M N x ⟶ T :=
  (signedSwap (M.obj (op x)) (N.obj x)).hom ≫ b (op x)

lemma swapFamilyApp_element (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (b : ∀ x, objectFamily A Dᵒᵖ N.toRightOpposite M.toFunctor x ⟶ T) (x : D)
    {r s n : ℤ} (m : (M.obj (op x)).X r) (t : (N.obj x).X s) (hn : r + s = n) :
    familyElement A D (swapFamilyApp A D M N b) x m t hn =
      (r * s).negOnePow • familyElement A Dᵒᵖ b (op x) t m (by omega) := by
  change (b (op x)).f n ((signedSwap (M.obj (op x)) (N.obj x)).hom.f n
    (ιTensorObj (M.obj (op x)) (N.obj x) r s n hn (m ⊗ₜ[A] t))) = _
  rw [signedSwap_apply]
  simp only [familyElement, Units.smul_def, map_zsmul]
  rfl

/-- 元の族をsigned braidingでopposite上のtensor順序へ移す。 -/
def unswapFamilyApp (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T) (x : Dᵒᵖ) :
    objectFamily A Dᵒᵖ N.toRightOpposite M.toFunctor x ⟶ T :=
  (signedSwap (N.obj x.unop) (M.obj x)).hom ≫ a x.unop

lemma unswapFamilyApp_element (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (a : ∀ x, objectFamily A D M N x ⟶ T) (x : Dᵒᵖ)
    {s r n : ℤ} (t : (N.obj x.unop).X s) (m : (M.obj x).X r) (hn : s + r = n) :
    familyElement A Dᵒᵖ (unswapFamilyApp A D M N a) x t m hn =
      (s * r).negOnePow • familyElement A D a x.unop m t (by omega) := by
  change (a x.unop).f n ((signedSwap (N.obj x.unop) (M.obj x)).hom.f n
    (ιTensorObj (N.obj x.unop) (M.obj x) s r n hn (t ⊗ₜ[A] m))) = _
  rw [signedSwap_apply]
  simp only [familyElement, Units.smul_def, map_zsmul]

/-- opposite上のbalanced族から元のbalanced族へ。 -/
def swapFamily (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (b : BalancedFamily A Dᵒᵖ N.toRightOpposite M.toFunctor T) : BalancedFamily A D M N T := by
  refine balancedFamilyMk A D (swapFamilyApp A D M N b.val) ?_
  intro x y r p s n hn m f t
  rw [swapFamilyApp_element, swapFamilyApp_element]
  have hb := balancedFamily_element_of_sums A Dᵒᵖ b (op y) (op x)
    (i := p + s) (j := r + p) (n := n) (by omega) rfl (by omega) t f m
  rw [leftToRightOpposite_action, rightToLeft_action] at hb
  rw [← hb]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : r * p + ((r + p) * s + s * p) = r * (p + s) + 2 * (p * s) := by ring
  rw [hs, Int.negOnePow_add (r * (p + s)) (2 * (p * s)), Int.negOnePow_two_mul, mul_one]

/-- 元のbalanced族からopposite上のbalanced族へ。 -/
def unswapFamily (M : RightModule A D) (N : LeftModule A D) {T : Complex A}
    (a : BalancedFamily A D M N T) : BalancedFamily A Dᵒᵖ N.toRightOpposite M.toFunctor T := by
  refine balancedFamilyMk A Dᵒᵖ (unswapFamilyApp A D M N a.val) ?_
  intro x y s p r n hn t f m
  rw [unswapFamilyApp_element, unswapFamilyApp_element,
    leftToRightOpposite_action, rightToLeft_action]
  have ha := balancedFamily_element_of_sums A D a y.unop x.unop
    (i := p + r) (j := s + p) (n := n) (by omega) rfl (by omega) m f t
  rw [← ha]
  simp only [smul_smul, ← Int.negOnePow_add]
  have hs : s * p + ((s + p) * r + r * p) = s * (p + r) + 2 * (r * p) := by ring
  rw [hs, Int.negOnePow_add (s * (p + r)) (2 * (r * p)), Int.negOnePow_two_mul, mul_one]

/-- 符号付き交換はbalanced族の同値を与える。 -/
def swapFamilyEquiv (M : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    BalancedFamily A D M N T ≃ BalancedFamily A Dᵒᵖ N.toRightOpposite M.toFunctor T where
  toFun := unswapFamily A D M N
  invFun := swapFamily A D M N
  left_inv a := by
    apply Subtype.ext
    funext x
    change (signedSwap (M.obj (op x)) (N.obj x)).hom ≫
      (signedSwap (N.obj x) (M.obj (op x))).hom ≫ a.val x = a.val x
    rw [← Category.assoc, SerrePositivity.cochainTensorSymmetry_hom_comp]
    exact Category.id_comp _
  right_inv b := by
    apply Subtype.ext
    funext x
    change (signedSwap (N.obj x.unop) (M.obj x)).hom ≫
      (signedSwap (M.obj x) (N.obj x.unop)).hom ≫ b.val x = b.val x
    rw [← Category.assoc, SerrePositivity.cochainTensorSymmetry_hom_comp]
    exact Category.id_comp _

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end SwapFamilies

/-! ## Swap（旧 SerrePositivity/DifferentialGraded/Tensor/Swap.lean） -/

/-! # opposite上のbalanced tensorとの符号付き交換同型 -/

@[expose] public section Swap
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左右の因子を交換し、Dᵒᵖ上のbalanced tensorへ降ろす。 -/
def swapHom (M : RightModule A D) (N : LeftModule A D) :
    obj A D M N ⟶ obj A Dᵒᵖ N.toRightOpposite M.toFunctor :=
  desc A D M N (swapFamily A D M N
    ⟨ι A Dᵒᵖ N.toRightOpposite M.toFunctor, condition A Dᵒᵖ N.toRightOpposite M.toFunctor⟩)

/-- opposite上のtensorから元の順序へ戻す。 -/
def unswapHom (M : RightModule A D) (N : LeftModule A D) :
    obj A Dᵒᵖ N.toRightOpposite M.toFunctor ⟶ obj A D M N :=
  desc A Dᵒᵖ N.toRightOpposite M.toFunctor
    (unswapFamily A D M N ⟨ι A D M N, condition A D M N⟩)

@[reassoc (attr := simp)]
lemma ι_swapHom (M : RightModule A D) (N : LeftModule A D) (x : D) :
    ι A D M N x ≫ swapHom A D M N =
      (signedSwap (M.obj (op x)) (N.obj x)).hom ≫
        ι A Dᵒᵖ N.toRightOpposite M.toFunctor (op x) :=
  ι_desc A D M N _ x

@[reassoc (attr := simp)]
lemma ι_unswapHom (M : RightModule A D) (N : LeftModule A D) (x : Dᵒᵖ) :
    ι A Dᵒᵖ N.toRightOpposite M.toFunctor x ≫ unswapHom A D M N =
      (signedSwap (N.obj x.unop) (M.obj x)).hom ≫ ι A D M N x.unop :=
  ι_desc A Dᵒᵖ N.toRightOpposite M.toFunctor _ x

lemma swapHom_element (M : RightModule A D) (N : LeftModule A D) (x : D)
    {r s n : ℤ} (m : (M.obj (op x)).X r) (t : (N.obj x).X s) (hn : r + s = n) :
    (swapHom A D M N).f n (element A D M N x m t hn) =
      (r * s).negOnePow • element A Dᵒᵖ N.toRightOpposite M.toFunctor (op x) t m (by omega) := by
  have h := element_postcompose A D M N x (swapHom A D M N)
    (swapFamilyApp A D M N (ι A Dᵒᵖ N.toRightOpposite M.toFunctor) x)
    (ι_swapHom A D M N x) m t hn
  exact h.trans (swapFamilyApp_element A D M N _ x m t hn)

lemma unswapHom_element (M : RightModule A D) (N : LeftModule A D) (x : Dᵒᵖ)
    {s r n : ℤ} (t : (N.obj x.unop).X s) (m : (M.obj x).X r) (hn : s + r = n) :
    (unswapHom A D M N).f n (element A Dᵒᵖ N.toRightOpposite M.toFunctor x t m hn) =
      (s * r).negOnePow • element A D M N x.unop m t (by omega) := by
  have h := element_postcompose A Dᵒᵖ N.toRightOpposite M.toFunctor x (unswapHom A D M N)
    (unswapFamilyApp A D M N (ι A D M N) x) (ι_unswapHom A D M N x) t m hn
  exact h.trans (unswapFamilyApp_element A D M N _ x t m hn)

/-- 任意可換環上の非有界balanced tensorのopposite交換同型。 -/
def swapIso (M : RightModule A D) (N : LeftModule A D) :
    obj A D M N ≅ obj A Dᵒᵖ N.toRightOpposite M.toFunctor where
  hom := swapHom A D M N
  inv := unswapHom A D M N
  hom_inv_id := by
    apply hom_ext A D M N
    intro x
    rw [ι_swapHom_assoc, ι_unswapHom, ← Category.assoc,
      SerrePositivity.cochainTensorSymmetry_hom_comp]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  inv_hom_id := by
    apply hom_ext A Dᵒᵖ N.toRightOpposite M.toFunctor
    intro x
    rw [ι_unswapHom_assoc, ι_swapHom, ← Category.assoc,
      SerrePositivity.cochainTensorSymmetry_hom_comp]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end Swap

/-! ## SwapNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/SwapNaturality.lean） -/

/-! # balanced tensor交換の左加群射に関する自然性 -/

@[expose] public section SwapNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma swapHom_naturality_left (M : RightModule A D) {N N' : LeftModuleCategory A D}
    (g : N ⟶ N') :
    map A D (𝟙 (ForgetEnrichment.of (Complex A) M)) g ≫
      swapHom A D M (ForgetEnrichment.to (Complex A) N') =
    swapHom A D M (ForgetEnrichment.to (Complex A) N) ≫
      map A Dᵒᵖ ((leftModuleToRightOpposite A D).map g)
        (𝟙 (ForgetEnrichment.of (Complex A) M.toFunctor)) := by
  apply hom_ext A D M (ForgetEnrichment.to (Complex A) N)
  intro x
  let gx : (ForgetEnrichment.to (Complex A) N).obj x ⟶
      (ForgetEnrichment.to (Complex A) N').obj x := (leftModuleEvaluation A D x).map g
  have h := ι_map A D (M := ForgetEnrichment.of (Complex A) M)
    (M' := ForgetEnrichment.of (Complex A) M) (𝟙 _) g x
  simp only [CategoryTheory.Functor.map_id] at h
  change ι A D M (ForgetEnrichment.to (Complex A) N) x ≫
      map A D (𝟙 (ForgetEnrichment.of (Complex A) M)) g =
    (𝟙 (M.obj (op x)) ⊗ₘ gx) ≫ ι A D M (ForgetEnrichment.to (Complex A) N') x at h
  have h' := ι_map A Dᵒᵖ (N := ForgetEnrichment.of (Complex A) M.toFunctor)
    (N' := ForgetEnrichment.of (Complex A) M.toFunctor)
    ((leftModuleToRightOpposite A D).map g) (𝟙 _) (op x)
  simp only [CategoryTheory.Functor.map_id, leftModuleToRightOpposite_map_eval] at h'
  change ι A Dᵒᵖ (ForgetEnrichment.to (Complex A) N).toRightOpposite M.toFunctor (op x) ≫
      map A Dᵒᵖ ((leftModuleToRightOpposite A D).map g)
        (𝟙 (ForgetEnrichment.of (Complex A) M.toFunctor)) =
    (gx ⊗ₘ 𝟙 (M.obj (op x))) ≫
      ι A Dᵒᵖ (ForgetEnrichment.to (Complex A) N').toRightOpposite M.toFunctor (op x) at h'
  calc
    _ = (𝟙 (M.obj (op x)) ⊗ₘ gx) ≫
        (signedSwap (M.obj (op x)) ((ForgetEnrichment.to (Complex A) N').obj x)).hom ≫
          ι A Dᵒᵖ (ForgetEnrichment.to (Complex A) N').toRightOpposite M.toFunctor (op x) := by
      rw [← Category.assoc, h, Category.assoc, ι_swapHom]
    _ = (signedSwap (M.obj (op x)) ((ForgetEnrichment.to (Complex A) N).obj x)).hom ≫
        (gx ⊗ₘ 𝟙 (M.obj (op x))) ≫
          ι A Dᵒᵖ (ForgetEnrichment.to (Complex A) N').toRightOpposite M.toFunctor (op x) := by
      rw [← Category.assoc, signedSwap_naturality, Category.assoc]
    _ = _ := by
      rw [ι_swapHom_assoc, h']

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end SwapNaturality
