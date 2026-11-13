module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor

/-! # 係数制限と dg nerve

概要：係数を制限しても dg nerve は変わらない。
方針：Hom の元と微分は同じであり、豊穣合成と単位も同じ元を与えることを使う。
規約：環準同型は任意。使われ方：導来底変更の値域の係数を戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open _root_.CategoryTheory MonoidalCategory _root_.SerrePositivity.DifferentialGraded _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded.ScalarExtension
variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 概要：T 上の dg 圏を S 上に係数制限する。
方針：係数制限の lax monoidal 構造で豊穣構造を移送する。
規約：対象と Hom の元は変えない。使われ方：異なる係数環間の dg 関手。 -/
abbrev DGRestrictScalars (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory T D] : Type v :=
  TransportEnrichment (restriction f) D

variable {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory T D]

/-- 概要：係数制限後の通常順合成は元の合成と一致する。
方針：係数制限の tensorator を純粋テンソル上で評価する。
規約：Koszul 符号は整数の作用。使われ方：単体の方程式の保存。 -/
lemma restrictScalars_compose {x y z : D} {p q n : ℤ}
    (g : _root_.SerrePositivity.DifferentialGraded.GradedHom T y z q) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom T x y p) (hpq : p + q = n) :
    _root_.SerrePositivity.DifferentialGraded.compose S (D := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f D) g h hpq = _root_.SerrePositivity.DifferentialGraded.compose T g h hpq := by
  unfold _root_.SerrePositivity.DifferentialGraded.compose forward
  change (p * q).negOnePow • (eComp (Complex T) x y z).f n
    ((Functor.LaxMonoidal.μ (restriction f) _ _).f n
      (ιTensorObj ((restriction f).obj (homObject T D x y))
        ((restriction f).obj (homObject T D y z)) p q n hpq (h ⊗ₜ[S] g))) = _
  rw [restriction_μ_apply]

/-- 概要：係数制限後の閉零単位は元の単位と同じ元を持つ。
方針：lax monoidal 単位射の 1 上の値を用いる。
規約：Hom の underlying 元の等式。使われ方：退化写像との可換性。 -/
lemma restrictScalars_unit (x : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f D) :
    (_root_.SerrePositivity.DifferentialGraded.unitElement S x).val = (_root_.SerrePositivity.DifferentialGraded.unitElement T (D := D) x).val := by
  change (eId (Complex T) (C := D) x).f 0
    ((Functor.LaxMonoidal.ε (restriction f)).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat S))).inv (1 : S))) = _
  rw [restriction_ε_one]
  rfl

/-- 概要：単体データを元を変えずに係数制限する。
方針：頂点族と全斉次成分をそのまま取る。
規約：Hom の型は定義上同じ。使われ方：単体の係数制限。 -/
abbrev restrictScalarsData {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData T D n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData S (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f D) n := ⟨s.obj, s.hom⟩

/-- 概要：係数制限は HA 方程式の右辺を変えない。
方針：有限和の各項で通常順合成の比較を使う。
規約：元の加法群は同一。使われ方：係数制限した単体の方程式。 -/
lemma restrictScalars_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData T D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsData f s).rhs I a b k hI ha hb hk = s.rhs I a b k hI ha hb hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsData]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalars_compose]
  · rfl

/-- 概要：T 上の単体を S 上の単体として読む。
方針：微分は同一であり右辺の比較で方程式を移す。
規約：対象も射の元もそのまま。使われ方：nerve の係数制限同型。 -/
def restrictScalarsSimplex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex T D n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f D) n where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsData f s.toSimplexData
  equation I a b k hI ha hb hk := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalars_rhs]
    exact s.equation I a b k hI ha hb hk

/-- 概要：係数制限した dg 圏の単体を T 上に戻す。
方針：同じデータの右辺比較を逆向きに使う。
規約：線形性に新しい条件は不要。使われ方：nerve 同型の逆射。 -/
def unrestrictScalarsSimplex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f D) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex T D n where
  obj := s.obj
  hom := s.hom
  equation I a b k hI ha hb hk := by
    let t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData T D n := ⟨s.obj, s.hom⟩
    exact (s.equation I a b k hI ha hb hk).trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalars_rhs f t I a b k hI ha hb hk)

/-- 概要：係数制限は単体の任意の引き戻しと可換である。
方針：単射の場合と零成分は同一、潰れた辺では単位の比較を使う。
規約：HA の三分岐による引き戻し。使われ方：nerve 同型の自然性。 -/
lemma restrictScalarsSimplex_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex T D n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsSimplex f (s.pullback α) = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsSimplex f s).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  apply heq_of_eq
  funext J a b k hJ ha hb hk
  change (s.toSimplexData.pullback α).hom J a b k hJ ha hb hk =
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsData f s.toSimplexData).pullback α).hom J a b k hJ ha hb hk
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  · by_cases hc : J.card = 2
    · have hk0 : k = 0 := by omega
      subst hk0
      have hab : α a = α b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
        (by rw [ha]; exact J.isLeast_min' _) (by rw [hb]; exact J.isGreatest_max' _)
      have hl := s.pullback_hom_of_collapsed_pair α J a b 0 hJ ha hb hk hi hc
      have hr := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsSimplex f s).pullback_hom_of_collapsed_pair
        α J a b 0 hJ ha hb hk hi hc
      exact eq_of_heq (hl.trans
        ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalars_unit f (s.obj (α b)))).symm.trans hr.symm))
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc]

/-- 概要：係数制限した dg 圏の dg nerve は元の nerve と同型である。
方針：各単体を同じ頂点と斉次元の族で双方向に読む。
規約：環準同型は任意。使われ方：S 線形 dg 関手から T 上の nerve への写像。 -/
def dgNerveRestrictScalarsIso (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory T D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars f D) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve T D :=
  (NatIso.ofComponents (fun _ => {
    hom := ↾fun s => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsSimplex f s
    inv := ↾fun s => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.unrestrictScalarsSimplex f s
    hom_inv_id := by ext s; apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext; rfl
    inv_hom_id := by ext s; apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext; rfl }) (by
      intro m n α
      ext s
      exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.restrictScalarsSimplex_pullback f s α.unop.toOrderHom)).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.1.3"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGRestrictScalars
attribute [cite HA "1.3.1.3"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerveRestrictScalarsIso
