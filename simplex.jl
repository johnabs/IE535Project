
# simplex::
# This runs both phases of the simplex method using the objective coefficients,
# polyhedral set matrix, and right hand side to construct the tableau later in the process.
# Note, we're storing results as successful or failure in each phase to make life easier
# in this simplex function as the booleans are already computed in the phase 1 and 2 stages for feasibility.
function simplex(A,b,c,type)
# First run phase 1; if it returns true then proceed to phase 2:
# otherwise, we're done.
    # If b is positive and we have an identity, we skip phase 1 since we know we have at least 1 BFS.
    # Check if we already have a BFS; if so, we don't need phase 1.
    obj=c
    if(type=="max")
        c= -1 .* c
    end
    res=phase1(A,b,c)
    # Finally we recompute any reduced costs that are needed to pass this
    # tableau to phase 2.
    if(res[1])
        mat,a_inds,old_c,new_b=res[2]
        # Pivot handles recession directions if needed, and returns an
        # error if it occurs, so this is phase2.
        mat=p1_to_p2(mat,old_c,a_inds,type)
        printstyled("Beginning pivoting for Phase 2:\n",color=:blue)
        res2=pivot(mat)
    else
        printstyled(res[2]*".\n",color=:red,bold=true)
        return nothing
    end
    # If our phase 2 had a recession direction, it returns a string.
    # So if it's not a string, we know it's optimal.
    if(typeof(res2)!=String && res2!=nothing)
        display(res2)
        temp=find_basis_indices(res2)
        optimal_bfs=Rational.(zeros(size(res2,2)-1))
        optimal_bfs[temp]=(res2[2:end,end])
        printstyled("Problem is solved.\n",color=:green)
        printstyled("The optimal solution is ", color=:green)
        printstyled("["*join(string.(optimal_bfs),", ")*"],\n",color=:cyan)
        printstyled("and the optimal objective value is ",color=:green)
        printstyled(string(obj'*optimal_bfs),color=:cyan);
        print(".\n")
        return(res2,optimal_bfs,obj'*optimal_bfs)
    # Otherwise, we print the error message, and return nothing.
    elseif res2!=nothing
        printstyled(res2*".\n",color=:red,bold=true)
        return nothing
    end
end


# This function takes us from the phase 1 tableau to the phase 2 tableau.
function p1_to_p2(m1,c,a_inds,type)
        temp=find_basis_indices(m1)
        println(temp)
        println(a_inds)
        # Check if any artifical variables are in the basis
        if(any(a_inds .∈ [temp,] ))
            println("ARTIFICIALS IN THE BASIS!!!")
        # If not, just delete them and adjust the tableau accordingly:
        else
            #display(m1)
            kinds= (1:size(m1,2))[(1:size(m1,2) .∉ [a_inds,])]
            println("KINDS")
            #display(m1[:,kinds])
            mat=m1[:,kinds]
            println("MAT")
            printstyled("Removed artificial varibles:\n",color=:blue,blink=false)
            display(mat)
            mat[1,1:end-1]=(-1 .* c)
            println("MAT2")
            mat[1,end]=0
            println("ZEROED")
            printstyled("Adjusted reduced cost row:\n",color=:blue,blink=false)
            display(mat)

            for i in 1:(size(mat,2))-1
                if i ∈ temp && mat[1,i]!=0
                    t=findfirst(x->x!=0,mat[2:end,i])+1
                    row=deepcopy(mat[t,:])
                    scalar=(-1*mat[1,i])/mat[t,i]
                    #mat[1,:]= mat[1,:]+(((mat[i,1]>0 && scalar>0) || (mat[i,1]<0 && scalar<0)) ? -1 .* (row*scalar) : row*scalar)
                    mat[1,:]= mat[1,:]+row*scalar
                end
            end
            printstyled("Recomputed reduced cost row\n",color=:blue,blink=false)

        end
        # Pretty print the intermediate matrices after each pivot.
        printstyled("Reconstructed tableau for phase 2 is:\n",color=:blue)
        display(mat)
        return(mat)
end

# Find the smallest value strictly greater than 0 and less than infinity.
function pos_min(x)
    if(length(filter(x->x>=0 && x!=Inf,x))==0)
        return nothing
        else
        return minimum(filter(x->x>=0 && x!=Inf,x))
    end
end

# Find the ties of any positive minima.
function tie_min(y)
    if(pos_min(y)==nothing)
        return false
    else
       return findall(x->x==pos_min(y),y)
    end
end

# Find any matches in the ratio test where integer division would fail:
# namely 0//0 (0/0 in Floating point arithmetic is handled as NaN, but fails
# with integer division so I have to handle it separately).
function match_zeros(z,y)
     if any(findall(x->x==0,z).∈ [findall(x->x==0,y),])
         return z.==0 .&& y.==z
    else
         return false
    end
end

#Deal with all funky zeros and NaNs
function match_zeros(z,y)
     if any(findall(x->x==0,z).∈ [findall(x->x==0,y),])
         return z.==0 .&& y.==z
    else
         return false
    end
end

# pivot:: Matrix{Rational} => a -> a | a::Matrix{Rational}
# This finds the pivot based on Bland's rule: namely,
# find the first positive reduced cost to enter the basis,
# then the first index of any ties for the smallest positive ratio to leave.
function find_pivot(mat)
    # Find the first positive reduced cost value
    pcol=findfirst(x->x>0,mat[1,1:end-1])
    # Compute all the ratios
    # account for issues with possible undefined integer division with 0//0.
    # 0/0 is normally NaN, but intger division breaks with this so it had
    # to be handled separately 1//0, -1//0, and 0//1 are all handled normally.
    temp=match_zeros(mat[2:end,end], mat[2:end,pcol])
    if(any(temp))
        finds=(2:size(mat,1))[temp]
        rinds=(2:size(mat,1))[.!(temp)]
        ratio=zeros(size(mat,1)-1)
        ratio[rinds.-1]=mat[rinds,end]./mat[rinds,pcol]
        ratio[finds.-1].=Inf
        ratio[findall(x->x<0,mat[2:end,pcol])].=Inf
    else
        # If there are no 0//0 errors, just compute ratios normally
        rinds=2:size(mat,1)
        ratio=mat[rinds,end]./mat[rinds,pcol]
        ratio[findall(x->x<0,mat[2:end,pcol])].=Inf
    end
    # Find the first index of the minimum ratios including ties.
    prow=tie_min(ratio)[1]+1
    # Julia allows me to return a vector and assign to two separate variables, which I leverage
    # here when this function is called in the pivot function.
    return ([prow,pcol])
end

# This finds basis indices based on columns that look like the identity matrix
# and that have a 0 in the reduced cost row, which makes things more accurate.
function find_basis_indices(mat)
    return(map(x->findfirst(y->y==vcat(0,I(size(mat,1)-1)[:,x]),eachcol(mat[:,1:end-1])),1:size(mat,1)-1))
end

# This finds basis indices based on columns that look like the identity matrix;
# however, since we don't have a reduced cost row, it defaults to the last most
# columns instead of the first, to prioritize artificial variables that are
# added in phase 1.
function find_basis_indices_start(mat)
    return(map(x->findlast(y->y==I(size(mat,1))[:,x],eachcol(mat)),1:size(mat,1)))
end

# feasibility_check:: [Matrix{Rational}] => b | a::Matrix{Rational}, b::Boolean
function feasibility_check(mat)
    # xi is the index of the first column that has a positive reduced cost,
    # but entirely negative entires elsewhere, excluding the right-hand-side column.
    # This indicates an unbounded problem.
    xi=findfirst(x-> x[1]>0 && all(x[2:end].<=0), eachcol(mat[1:end,1:end-1]))
    if(xi != nothing )#|| find_pivot(mat)==false)
        # If the problem is infeasible, we construct our basic feasible solution and recession direction.
        # The basic-feasible-indices are computed by matching to the identity matrix
        # the solution is then constructed by extracting the right hand side from the tableau for the
        # variable, and the recession direction is constructed by negating the all negative column
        # and making everything else 0, except the element that corresponds to the all negative column
        # which becomes a 1.
        bfi=map(x->findfirst(y->y==I(size(mat,1)-1)[:,x],eachcol(mat[2:end,1:end-1])),1:size(mat,1)-1)
        bfs=map(x-> in(x, bfi) ? mat[2:end,:][findfirst(y->y==x,bfi),end] : 0//1, 1:size(mat,2)-1)
        rd=map(x-> in(x, bfi) ? -1 .* mat[2:end,xi][findfirst(y->y==x,bfi),end] : 0//1, 1:length(bfs))
        rd[xi]=1//1
        err_msg="Problem is unbounded, the recession direction in order (i.e. x1->xn) is \n"* string(bfs)*" +x_"*string(xi)*"*"*string(rd)
        return([false,err_msg])
    end
    # If we can't find a positive reduced cost with negative column or invalid pivot, we are still feasible.
    return([true,nothing])
end


# pivot:: [Matrix{Rational},Vector{Vector{Int}}] => [a,b] -> [a,b] | a::Matrix{Rational}, b::Vector{Vector{Int}}
# First this function uses the find_pivot function to find our pivot index by one of the non-looping rules,
# then uses pivots the matrix, returning the modified matrix with the new basis.
function pivot(mat)
    # While any of the reduced costs (not including the right hand side) are greater than 0, keep
    # pivoting.
    mat=Rational.(mat)
    count=0
    while (any(mat[1,1:end-1].>0) && feasibility_check(mat)[1])
        #if(phase[1]==1)
        #    if(any(phase[2] .∈ [find_basis_indices(mat),]) && count<length(phase[2]))
        #        prow,pcol=find_pivot_artificial(mat,phase[2])
        #        count=count+1
        #    else
        #        prow,pcol=find_pivot(mat)
        #    end
        #else
        prow,pcol=find_pivot(mat)
        #end
        #if(ind!=[])
        #    prow,pcol=ind
        #end
        #println("Our pivot index for this is row "*string(prow)*" and column "*string(pcol)*".")
        # Go ahead and normalize our pivot row by the pivot index, it makes it easier to compute the
        # the scalar needed for the elementary row operations in the upcoming loop also assign it
        # to a variable to save on indexing operations.
        mat[prow,:]=mat[prow,:]./mat[prow,pcol]
        #println("test1")
        # Assign to placeholder for cleaner code below
        row=mat[prow,:]
        #println("row is "*string(row))
        # Placeholder for pivoted matrix
        sol=[]
        # Iterate over each row, do elementary row operations if we're not on the already re-scaled pivot row.
        # Add all results to the solutions vector.
        for i in collect(eachrow(mat))
            if i == row
                push!(sol, row)
            else
                scalar=i[pcol]
                #push!(sol, ((i[pcol]>0 && scalar>0) || (i[pcol]<0 && scalar<0)) ? i-row*scalar : i+row*scalar)
                push!(sol,  i-row*scalar )
            end
        end
        # Reconstruct the matrix from the solutions vector via hcat and transposing (vectors in julia
        # are column vectors by default, hence the need to transpose).
        mat=Matrix(reduce(hcat,sol)')
        # Pretty print the intermediate matrices after each pivot.
    end
    display(mat)
    # Once we're done pivoting, return the result.
    temp=feasibility_check(mat)
    if(temp[1])
        return(mat)
    else
        return temp[2]
    end
end

# add_artificial_variables:: Matrix{Rational} => a -> a | a::Matrix{Rational}
# Create an identity matrix, and append it to the matrix rows to force
# full row rank, and a basis for phase 1 of the method. Note, we're just
# adding artificial variables indiscriminately, not considering any
# potential bases in the original problem. This helps detect redundant
# constraints.
function add_artificial_vars(mat)
    res=find_basis_indices_start(mat)
    #println(res)
    if(nothing ∉ res)
        lc=mat[:,end]
        mat=mat[:,1:end-1]
        return([hcat(mat,I(size(mat,1))[:,1],lc), [size(mat,2)+1]])
    else
        #println("else")
        lc=mat[:,end]
        mat=mat[:,1:end-1]
        num=length(findall(x->x==nothing, res))
        inds=[]
       for i in findall(x->x==nothing, res)
           #println(i)
           t=Rational.(I(size(mat,1)))[:,i]
           #println(t)
           mat=hcat(mat,t)
           push!(inds,size(mat,2))
        end
        mat=hcat(mat,lc)
    end
        return([mat,inds])
end

# phase1 :: Matrix{Rational} => a -> [a,b,s] | a::Matrix{Rational}, b::Boolean, s:Message
# Phase one of the two-phase simplex:
function phase1(A,b,c;debug=false)
    # First add as many artificial variables as needed (the number of rows in A to guarantee full row rank), and note how many.
    printstyled("Beginning Phase 1:\n",color=:blue)
    if(any(b.< 0))
        ind=findall(x->x<0,b)
        b[ind]=b[ind] .* -1
        A[ind,:]=A[ind,:] .* -1
    end
    mat=Rational.(hcat(A,b))

    m2,a_inds=add_artificial_vars(mat);
    printstyled("Tableau with added artificial variables and constraints created:\n",color=:blue)
    display(m2)
    println(a_inds)

    #
    old_c=Rational.(c)
    c=Rational.(zeros(size(m2,2)))
    #println("Test1")
    #println(a_inds)
    c[a_inds].=1//1


    # Next, get the indices of these artificial variables that will act as a basis,
    # and the non-basis variables.
    #println("Test2")
    r0=Rational.(zeros(size(m2,2)))'
    #display(r0)
    r0[a_inds].=-1
    #display(r0)
    rinds=map(x->findfirst(y->y==1,m2[:,x]),a_inds)
    #display(rinds)
    #display(m2[rinds,:])
    #display(sum(m2[rinds,:],dims=1))
    r0=r0.+sum(m2[rinds,:],dims=1)
    #display(r0)
    #r0[n_ind]=Rational.(c[b_ind]'*m2[:,n_ind]-c[n_ind]')
    #r0[end]=c[b_ind]'*b
    m2=vcat(r0,m2)
    printstyled("Complete tableau with reduced costs created:\n",color=:blue)
    display(m2)


    # Compute the objective function row for the matrix based on the new problem,
    # namely, minimizing the sum of the artificial variables
    #z=hcat(ones(num_art)'*I(num_art)*m2[:,n_ind],zeros(num_art)')
    #z=Matrix(vcat(zeros(n_ind[end]),zeros(b_ind[end]) .- 1,0)')+sum(m2,dim=1)
    #rhs=[]
    #m2=vcat(z,m2)
    #m2=hcat(m2,rhs)
    #cb=[b_ind]

    # The pivot function has checks for termination and is a fixed point function
    # when the result of the last iteration is the same is the current iteration,
    # we know we're done pivoting.
    printstyled("Beginning Phase 1 pivoting:\n",color=:blue)
    res=pivot(m2)
    if(debug)
        return res
    end

    # Check if we have a recession direction here.
    if(typeof(res)==String)
        return([false, res])
    end

    # Check for redundant constraints, first find all non-artificial columns
    # according to the book if the row contains all 0s for legitimate variables
    # and for the rhs, it is redundant (see page 164 of the BJS book).
    temp=filter(x->x ∉ a_inds,1:size(m2,2))
    temp2=findall(x->x[temp]==zeros(size(temp)),eachrow(res[2:end,:])).+1
    # If there are any redundant constraints, we remove them, and
    # recompute any necessary values for our tableau.
    if(length(temp2)>0)
        output="Problem contains redundant constraints, namely row(s) "*join(string.(temp2),", ")*". Redundant constraints will be removed.\n"
        printstyled(output,color=:blue)
        res=res[1:end .!=temp2,:]
        display(res)
        new_b=find_basis_indices(res)
        new_n=filter(x->x ∉ new_b && x ∉ a_inds, 1:size(m2,2)-1)
        res[1,new_n]=old_c[new_b]'*res[2:end,new_n]-old_c[new_n]
    end
    new_b=find_basis_indices(res)
    #display(res)

    # If there is no recession direction, and all our reduced costs are negative,
    # we have an optimal tableau, from here, we need to determine
    # if the right hand side is 0. If not, phase 1 has concluded, and the
    # original problem is infeasible.
    if(res[1,end]==0//1 && all(res[1,a_inds].<=0))
        printstyled("Problem is feasible, proceeding to phase 2.\n",color=:green)
        return([true,[res,a_inds,old_c,new_b]])
    else
        return([false,"Problem is infeasible: all reduced costs are negative and the sum of artificial variables is nonzero"])
    end
end



# Book Comparison Examples:
using HiGHS, JuMP, Test, LinearAlgebra, DataStructures

# Problem 3.28
A=[2 -3 -1 1 1 0 0 ; -1 2 2 -3 0 1 0 ; -1 1 -4 1 0 0 1]
b=[0,1,8]
c=[-3,2,-1,1,0,0,0]
simplex(A,b,c,"max")
# Result: recession direction exists and identified.

# Example 3.7, page 118.
A=[1 -2 1 0 ; -1 1 0 1]
b=[4,3]
c=[-1,-3,0,0]
simplex(A,b,c,"min")
# Result: recession direction exists and identified.

# Example 4.1, page 156.
A=[1 1 -1 0; -1 1 0 -1 ; 0 1 0 0]
b=[2,1,3]
c=[1,-2,0,0]
simplex(A,b,c,"min")
# Result: -6, which agrees with the book

# Example 4.4, page 158.
A=[1 1 1 0 ; 2 3 0 -1]
b=[4,18]
c=[1 1 1 0]
simplex(A,b,c,"min")
# Result: problem is infeasible, same as the book.

# Example 4.5, page 162.
A=[1 1 1 0 ; -1 1 2 0 ; 0 2 3 0 ; 0 0 1 1]
b=[6,4,10,2]
c=[-1,2,-3,0]
simplex(A,b,c,"min")
# Correctly identifies redundant constraint and remove it, proceeds to solve
# with optimal objective value of -4
#
# Example 4.6, page 166.
A=[1 1 -1 0 0; -1 1 0 -1 0 ; 0 1 0 0 1]
b=[2,1,3]
c=[1,-2,0,0,0]
simplex(A,b,c,"min");
# Correctly solves with optimal objective value of -6
#
# Example 4.7, page 170.
A=[1 1 2 1 0 0 ; -1 0 1 0 -1 0 ; 0 0 1 0 0 -1]
b=[4,4,3]
c=[-1,-3,1,0,0,0]
simplex(A,b,c,"min")
# Correctly identifies as infeasible.

# Comparison with commercial solvers:

#Initialize Model 2
A=[90 20 40 -1 0 0 ; 30 80 60 0 -1 0; 10 20 50 0 0 -1]
b=[200,180,150]
c=[35,30,25,0,0,0]
model=Model(HiGHS.Optimizer)
set_optimizer_attribute(model, "presolve", "off")
# Define decision variables
@variable(model, x[1:6]);
# Add constraints (in  this case simple matrix based ones)
# Note for problem 1 I need to double check I didn't transpose the A matrix incorrectly.
@constraint(model, A*x .== b );
@constraint(model, x .>= Rational.(zeros(6)) );
# Define the objective function
@objective(model, Min, c'*x);
# Optimize the model
optimize!(model)
res=simplex(A,b,c,"min");
if(raw_status(model) == "kHighsModelStatusOptimal")
    # Check if my model is sufficiently close to the HiGHS optimizer
    # note mine should be correct as I'm using rational arithemetic, with
    # unlimited precision, not floating point values.
    if(isapprox(res[3],objective_value(model),rtol=0.0001))
        printstyled("Success: Models are sufficiently close!\n",color=:green)
    else
        printstyled("Failure: Models are NOT sufficiently close!\n",color=:red)
    end
elseif(res==nothing)
        printstyled("Success: Both show unboundedness!",color=:green)
else
        printstyled("Failure: My algorithm disagrees with HiGHS.)",color=:red)
end

#Initialize Model 16
A=vcat(Rational.(
 [1 0 0 1 0 0 1 0 0 1 0 0 0 0 0 0 0 0;
   0 1 0 0 1 0 0 1 0 0 1 0 0 0 0 0 0 0;
   0 0 1 0 0 1 0 0 1 0 0 1 0 0 0 0 0 0;
   20 0 0 15 0 0 12 0 0 0 0 0 1 0 0 0 0 0;
   0 20 0 0 15 0 0 12 0 0 0 0 0 1 0 0 0 0;
   0 0 20 0 0 15 0 0 12 0 0 0 0 0 1 0 0 0;
   1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0;
   0 0 0 1 1 1 0 0 0 0 0 0 0 0 0 0 1 0;
   0 0 0 0 0 0 1 1 1 0 0 0 0 0 0 0 0 1]),
   Rational.( [1//750 -1//900 0//1 1//750 -1//900 0//1 1//750 -1//900 0 0 0 0 0 0 0 0 0 0]),
   Rational.( [1//750 0//1 -1//450 1//750 0//1 -1//450 1//750 0//1 -1//450  0 0 0 0 0 0 0 0 0]))
b=[750,900,450,13000,12000,5000,900,1200,750,0,0]
c=vcat([385,385,385,330,330,300,275,275,275],zeros(9))
model=Model(HiGHS.Optimizer)
set_optimizer_attribute(model, "presolve", "off")
# Define decision variables
@variable(model, x[1:18]);
# Add constraints (in  this case simple matrix based ones)
# Note for problem 1 I need to double check I didn't transpose the A matrix incorrectly.
@constraint(model, A*x .== b );
@constraint(model, x .>= Rational.(zeros(18)) );
# Define the objective function
@objective(model, Max, c'*x);
# Optimize the model
optimize!(model)
res=simplex(A,b,c,"max");
if(raw_status(model) == "kHighsModelStatusOptimal")
    # Check if my model is sufficiently close to the HiGHS optimizer
    # note mine should be correct as I'm using rational arithemetic, with
    # unlimited precision, not floating point values.
    if(isapprox(res[3],objective_value(model),rtol=0.0001))
        printstyled("Success: Models are sufficiently close!\n",color=:green)
    else
        printstyled("Failure: Models are NOT sufficiently close!\n",color=:red)
    end
elseif(res==nothing)
        printstyled("Success: Both models indicate unboundedness or infeasibility!",color=:green)
else
        printstyled("Failure: mine doesn't agree with HiGHS.",color=:red)
end



#Initialize Model 23
model=Model(HiGHS.Optimizer)
set_optimizer_attribute(model, "presolve", "off")
@variable(model, x[1:14]);
@constraint(model, ([9,6,8.5,12,3.5,16,16,26,24,41,34,45,0,0]./100)' *x >= 0.2);
@constraint(model, ([0.5,3,4,4.5,0,4,4,8.5,2,1.5,1,0.5,0,0]./100)' *x >= 0.03);
@constraint(model, ([20,16,2.5,12,0,8,10.5,9,8,13,8,6.5,0,0]./100)' *x <= 0.12);
@constraint(model, 0.01 <= ([0.7,2,0.02,0.1,0.6,0.1,0.1,0.15,0.3,0.1,0.35,0.2,36,32]./100)' *x <= 0.02);
@constraint(model, 0.006 <= ([0.05,0.1,0.25,0.4,0.1,0.9,1.2,0.6,0.65,1.2,0.8,0.6,0.5,14]./100)' *x <= 0.02);
@constraint(model, ([0.7,2,0.02,0.1,0.6,0.1,0.1,0.15,0.3,0.1,0.35,0.2,36,32]./100 .- [0.05,0.1,0.25,0.4,0.1,0.9,1.2,0.6,0.65,1.2,0.8,0.6,0.5,14]./100)' *x >= 0);
@constraint(model, x.>= [4,1,1,1,5,5,5,5,1,1,1,1,0,1]./100);
@constraint(model, x.<= [20,20,25,25,14,30,30,15,25,35,35,35,2,2]./100);
@constraint(model, sum(x) == 1);
@constraint(model, 0.05 <= x[1]+x[2]<= 0.20);
@constraint(model, 0.20 <= x[3]+x[4]<= 0.35);
@constraint(model, 0.10 <= x[6]+x[7]<= 0.30);
@constraint(model, 0.02 <= x[8]+x[9]<= 0.25);
@constraint(model, 0.03 <= x[10]+x[11]+x[12]<= 0.35);
@objective(model, Min, [64,35,55,54,19,64,62,77,66,74,85,108,10,66]'*x);
# Optimize the model
optimize!(model)
# I put my model into some external code to help formulate the matrices
# due to a series of typos making my life miserable since this matrix is so huge.
# BUT IT DOES WORK. The matrix of interest is in the test2.csv file, which contains
# A and b.
c=vcat(Rational.([64,35,55,54,19,64,62,77,66,74,85,108,10,66]),Rational.(zeros(60-14)))
A=readdlm("test2.csv", ',', String)
A=Meta.parse.(A)
A=eval.(A)
A=Rational.(A)
b=A[:,end]
A=A[:,1:end-1]
res=simplex(A,b,c,"min");
if(raw_status(model) == "kHighsModelStatusOptimal")
    # Check if my model is sufficiently close to the HiGHS optimizer
    # note mine should be correct as I'm using rational arithemetic, with
    # unlimited precision, not floating point values.
    if(isapprox(res[3],objective_value(model),rtol=0.0001))
        printstyled("Success: Models are sufficiently close!\n",color=:green)
    else
        printstyled("Failure: Models are NOT sufficiently close!\n",color=:red)
    end
elseif(res==nothing)
        printstyled("Success: Both models indicate unboundedness or infeasibility!",color=:green)
else
        printstyled("Failure: mine doesn't agree with HiGHS.",color=:red)
end
