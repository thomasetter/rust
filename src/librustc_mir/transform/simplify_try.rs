use crate::transform::{MirPass, MirSource};
use rustc::ty::{TyCtxt, Ty};
use rustc::mir::*;
use rustc_target::abi::VariantIdx;

/// Simplifies arms of form `Variant(x) => x` to just `x`.
///
/// This is done by transforming basic blocks where the statements match:
///
/// ```rust
/// _LOCAL_TMP = ((_LOCAL_1 as Variant ).FIELD: TY );
/// ((_LOCAL_0 as Variant).FIELD: TY) = move _LOCAL_TMP;
/// discriminant(_LOCAL_0) = VAR_IDX;
/// ```
///
/// into:
///
/// ```rust
/// _LOCAL_0 = move _LOCAL_1
/// ```
pub struct SimplifyArmIdentity;

impl<'tcx> MirPass<'tcx> for SimplifyArmIdentity {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, _src: MirSource<'tcx>, body: &mut Body<'tcx>) {
        for (idx, bb) in body.basic_blocks_mut().iter_mut().enumerate() {
            debug!("SimplifyArmIdentity - bb{} = {:?}", idx, bb);

            // Need 3 statements:
            let (s0, s1, s2) = match &mut *bb.statements {
                [s0, s1, s2] => (s0, s1, s2),
                _ => continue,
            };
            debug!("SimplifyArmIdentity - found three stmts");

            // Pattern match on the form we want:
            let (local_tmp_s0, local_1, vf_s0) = match match_get_variant_field(s0) {
                None => continue,
                Some(x) => x,
            };
            debug!("SimplifyArmIdentity - get");
            let (local_tmp_s1, local_0, vf_s1) = match match_set_variant_field(s1) {
                None => continue,
                Some(x) => x,
            };
            debug!("SimplifyArmIdentity - set");
            if local_tmp_s0 != local_tmp_s1 || vf_s0 != vf_s1 {
                continue;
            }
            match match_set_discr(s2) {
                Some((local, var_idx)) if local == local_0 && var_idx == vf_s0.var_idx => {}
                _ => continue,
            }
            debug!("SimplifyArmIdentity - set_discr");

            // Right shape; transform!
            match &mut s0.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    *place = local_0.into();
                    *rvalue = Rvalue::Use(Operand::Move(local_1.into()));
                }
                _ => unreachable!(),
            }
            s1.kind = StatementKind::Nop;
            s2.kind = StatementKind::Nop;
        }
    }
}

/// Match on:
/// ```rust
/// _LOCAL_INTO = ((_LOCAL_FROM as Variant).FIELD: TY);
/// ```
fn match_get_variant_field<'tcx>(stmt: &Statement<'tcx>) -> Option<(Local, Local, VarField<'tcx>)> {
    match &stmt.kind {
        StatementKind::Assign(box (place_into, rvalue_from)) => match rvalue_from {
            Rvalue::Use(Operand::Copy(pf)) | Rvalue::Use(Operand::Move(pf)) => {
                let local_into = place_into.as_local()?;
                let (local_from, vf) = match_variant_field_place(&pf)?;
                Some((local_into, local_from, vf))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Match on:
/// ```rust
/// ((_LOCAL_FROM as Variant).FIELD: TY) = move _LOCAL_INTO;
/// ```
fn match_set_variant_field<'tcx>(stmt: &Statement<'tcx>) -> Option<(Local, Local, VarField<'tcx>)> {
    match &stmt.kind {
        StatementKind::Assign(box (place_from, rvalue_into)) => match rvalue_into {
            Rvalue::Use(Operand::Move(place_into)) => {
                let local_into = place_into.as_local()?;
                let (local_from, vf) = match_variant_field_place(&place_from)?;
                Some((local_into, local_from, vf))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Match on:
/// ```rust
/// discriminant(_LOCAL_TO_SET) = VAR_IDX;
/// ```
fn match_set_discr<'tcx>(stmt: &Statement<'tcx>) -> Option<(Local, VariantIdx)> {
    match &stmt.kind {
        StatementKind::SetDiscriminant { place, variant_index } => Some((
            place.as_local()?,
            *variant_index
        )),
        _ => None,
    }
}

#[derive(PartialEq)]
struct VarField<'tcx> {
    field: Field,
    field_ty: Ty<'tcx>,
    var_idx: VariantIdx,
}

/// Match on `((_LOCAL as Variant).FIELD: TY)`.
fn match_variant_field_place<'tcx>(place: &Place<'tcx>) -> Option<(Local, VarField<'tcx>)> {
    match place.as_ref() {
        PlaceRef {
            base: &PlaceBase::Local(local),
            projection: &[ProjectionElem::Downcast(_, var_idx), ProjectionElem::Field(field, ty)],
        } => Some((local, VarField { field, field_ty: ty, var_idx })),
        _ => None,
    }
}

pub struct SimplifyBranchSame;

impl<'tcx> MirPass<'tcx> for SimplifyBranchSame {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, _src: MirSource<'tcx>, _body: &mut Body<'tcx>) {
        //debug!("SimplifyBranchSame - simplifying {:?}", _body);
    }
}
