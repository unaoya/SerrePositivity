module
public import SerrePositivity.DifferentialGraded.Bimodule.Identity
public import SerrePositivity.DifferentialGraded.Bimodule.PairedRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.QuasiIso
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable

/-! # dg関手のHom写像による対角bimoduleの制限比較

## 概要
dg関手のHom写像による対角bimoduleの制限比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
