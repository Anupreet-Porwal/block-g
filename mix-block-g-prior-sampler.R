library(invgamma)
library(WoodburyMatrix)
library(mvtnorm)
library(truncnorm)
library(extraDistr)
library(dirichletprocess)
resample <- function(x, ...) x[sample.int(length(x), ...)]

cluster_prop_llikelihood <- function(k,b, xtx, g, gam, sigma2, g_K, r,prior.corr){
  var_in_mod <- which(gam==1)
  ind.var <- var_in_mod[r]
  g[ind.var] <- g_K[k]
  ggam <- g[as.logical(gam)]
  #print(dim(diag(1/sqrt(ggam))))
  b_sqrtg <- t(b) %*% diag(1/sqrt(ggam),nrow = length(ggam),ncol = length(ggam))
  # CHECK THIS EQUATION IS CORRECT
  #print(dim(xtx[r,-r]))
  #print(dim(b_sqrtg[-r]))
  if(prior.corr==TRUE){
    d_ind <- 2* (xtx[r,-r] %*% b_sqrtg[1,-r])*b[r]/sqrt(ggam[r]) + 
      xtx[r,r] * b[r]^2/ggam[r]
  }else{
    d_ind <- b[r]^2/ggam[r]
  }
  prop_llik <- -0.5*log(ggam[r]) - d_ind/(2*sigma2)
  
  return(prop_llik)
}


# Taken from: https://github.com/IvanUkhov/blog/blob/main/_scripts/2021-01-25-dirichlet-process/common.R
# blog post: https://blog.ivanukhov.com/2021/01/25/dirichlet-process.html
count_subjects <- function(m, k) {

  n <- rep(0, m)
  if(length(k)==0){
   return(n) 
  }
  k <- as.data.frame(table(k))
  n[as.numeric(levels(k[ , 1]))[k[ , 1]]] <- k[ , 2]
  return (n)
}

stick_break <- function(l, alpha, beta,log=TRUE) {
  q <- rbeta(l, shape1 = alpha, shape2 = beta)
  q <- c(head(q, -1), 1)
  if(log==TRUE){
    p = log(q) + c(0, cumsum(log(1 - head(q, -1))))
  }else{
    p = q * c(1, cumprod(1 - head(q, -1)))
  }
  return(list(p=p,q=q))
}

sample_Plambda_prior <- function(l, alpha0 = 1, beta0 = 1) {
  rgamma(l, alpha0, beta0)
}

sample_Plambda_posterior <- function(l, q, alpha0 = 1, beta0 = 1) {
  sample_Plambda_prior(
    l = l,
    alpha0 = alpha0 + length(q) - 1,
    beta0 = beta0 - sum(log(head(q, -1)))
  )
}
# Taken from here :  https://github.com/willtownes/mit6882/blob/master/will/speed_tests.Rmd
# Some discussion here:  http://www.statsathome.com/2018/10/19/sampling-from-multivariate-normal-precision-and-covariance-parameterizations/
custom4<-function(n,theta,Lambda,D=length(theta)){
  Q<-chol(Lambda)
  Z<-matrix(rnorm(n*D),nrow=D,ncol=n)
  #using vector recycling tricks below
  #Q^{-1}*Z+Lambda^{-1}*theta == Q^{-1}*(Z+(Q')^{-1}*theta)
  backsolve(Q,Z+drop(backsolve(Q,theta,transpose=TRUE)))
}

rhyperg <- function(n,a){
  h <- rbeta(n,1,a/2-1)
  return(h/(1-h))
}

rhypergn <- function(x,a,n){
  h <- rbeta(x,1,a/2-1)
  return(n*h/(1-h))
}


rtgamma <- function(n, shape, rate, truncation){
  # Sampling fron truncated gamma involves three steps:
  
  # 1) Find the probability corresponding to truncation point 
  p_trunc = pgamma(truncation, shape = shape, rate = rate)
  # 2) Draw from uniform distribution with max = the probability of truncation point
  u_trucgam <- runif(n,0, p_trunc)
  # 3) Draw quantile corresponding to u_truncgam from the inverse gamma distribution
  t <- qgamma(u_trucgam,shape = shape, rate = rate)
  
  return(t)
}
#### Proposal function for gamma variable ####
proposal.gamma <- function(gam, d=4){
  p <- length(gam)
  prob1 <- c(0.4,0.3,0.2,0.1)#c(0.5,0.3,0.15,0.05)
  prob2 <- c(0.7,0.3)
  
  s <- resample(1:2,1, prob = prob2)
  # Use technique of George mchlloch stat sinaca paper  eq 46 if s==1
  
  if(s==1){
    if(p<d){
      d=p
      prob1 <- prob1[1:d]/sum(prob1[1:d])
    }
    d0 <- resample(1:d,1, prob=prob1)
    ind <- resample(1:p,d0)
    gam[ind]=!gam[ind]
    
    
    # swap one entry from active set with one entry from non-active set randomly
  }else if(s==2){
    if(all(gam==1)){
      ind <- resample(1:p,1)
      gam[ind]=0
    }else if(all(gam==0)){
      ind <- resample(1:p,1)
      gam[ind]=1
    }else{
      gam1 <- which(gam==1)
      gam0 <- which(gam==0)
      ind1 <- resample(gam1,1)
      ind0 <- resample(gam0,1)
      gam[ind1] <- 0
      gam[ind0] <- 1
    }
  }
  return(gam)
}


to_right_Matrix <- function(x) {
  symmetric <- FALSE
  if (is(x, 'diagonalMatrix')) {
    x
  } else {
    as(x, if (symmetric) 'symmetricMatrix' else 'Matrix')
  }
}

log_marginal <- function(x,y,g,gam,hyper.prior,prior.corr,tau2){
  
  n <- length(y)
  p <- ncol(x)
  #print(sum(gam))
  x <-  x[ ,as.logical(gam)]
  g <- g[as.logical(gam)]
  pgam <- sum(gam)
  if(length(g)==0){
    # Do calculation as if X and G are not there
    xtx <- xty <- g <-  NULL
    num1 <- sum((y-mean(y))^2)
    logmg <- lgamma((n-1)/2) - 0.5*log(n) - 
      0.5*(n-1)*log(pi)-0.5*(n-1)*log(num1)
  }else{
    # Calculate using our formula
    xtx <- t(x)%*% x
    xty <- t(x)%*% y
    
    if(hyper.prior=="beta-prime-MG"){
      ghalf <- diag(sqrt(g),nrow = pgam,ncol=pgam)
      xghalf <- x %*% ghalf
      if(prior.corr==TRUE){
        mat <- WoodburyMatrix(A=diag(n), X= sqrt(tau2)*xghalf, B=xtx)
      }else{
        mat <- WoodburyMatrix(A=diag(n), X= sqrt(tau2)*xghalf, B=diag(pgam))
      }
      
    }else{
      ghalf.inv <- diag(1/sqrt(g),nrow = pgam,ncol=pgam)
      # print(paste("min:",min(g)))
      # print(paste("max:",max(g)))
      if(prior.corr==TRUE){
        gxtxg <- ghalf.inv %*% xtx %*% ghalf.inv  
      }else{
        gxtxg <- diag(1/g,nrow = pgam,ncol=pgam)
      }
      gxtxg <- gxtxg/tau2
      gxtxg <- (gxtxg+t(gxtxg))/2
      # temp <- solve(xtx+gxtxg)
      # print(isSymmetric(temp))
      # B_parts <- if (!is.list(gxtxg)) list(gxtxg) else gxtxg
      # B_parts <- lapply(B_parts, to_right_Matrix)
      # print(gxtxg)
      # print("Done this calculation")
      mat <- WoodburyMatrix(A=diag(n), X= x , B=gxtxg)
      
    }
    
    # g_025 <- diag((g)^{0.25},nrow = pgam,ncol=pgam)
    # g_025_inv <- diag((g)^{-0.25},nrow = pgam,ncol=pgam)
    # mat <- WoodburyMatrix(A=diag(n), X= x %*% g_025, B= g_025_inv %*% xtx %*% g_025_inv)
    
    
    num1 <- as.numeric(y%*% solve(mat) %*% y - n*mean(y)^2)
    den <- as.numeric(determinant(mat, logarithm = TRUE)$modulus)
    logmg <- lgamma((n-1)/2) - 0.5*log(n) - 
      0.5*(n-1)*log(pi)-0.5*(n-1)*log(num1)-0.5*den
  }
  
  res <- list("logmg"=logmg, "xtx"=xtx, "xty"=xty, "ggam"=g, "sig2rate"=num1)
  return(res)
}


#### Algorithm 1 of Liu et al 2013 ####
gamma_rejection_sampler <- function(alpha, gam_param,truncation=NULL){
  if(is.null(truncation)){
    if(gam_param<=0){
      logdelta0 <- log(4*alpha)-2*log(sqrt(gam_param^2+4*alpha)+abs(gam_param))
      delta0 <- exp(logdelta0)
      
      t <- rgamma(1,shape = alpha, rate = delta0)
      u <- runif(1) # MADE A CHANGE IN WHILE CONDITION extra alpha 
      while (log(u) > alpha -t*(1-delta0)-2*sqrt(t)*gam_param-alpha/delta0){
        t <- rgamma(1,shape = alpha, rate = delta0)
        u <- runif(1)
      }
    }else{
      t <- rgamma(1,alpha,1)
      u <- runif(1) # log(u) > -2gamma*sqrt(t)
      while (log(u)> -2*gam_param*sqrt(t)) {

        t <- rgamma(1,alpha,1)
        u <- runif(1)
      }
    }
    
  }else{
    if(gam_param<=0){
      logdelta0 <- log(4*alpha)-2*log(sqrt(gam_param^2+4*alpha)+abs(gam_param))
      delta0 <- exp(logdelta0)
      
      t <- rtgamma(1,shape = alpha, rate = delta0,truncation = truncation)
      u <- runif(1) # made a change here in while loop
      
      while (log(u) > alpha-t*(1-delta0)-2*sqrt(t)*gam_param-alpha/delta0){

        t <- rtgamma(1,shape = alpha, rate = delta0,truncation = truncation)
        u <- runif(1)
      }
    }else{
      t <- rtgamma(1,shape=alpha,rate=1,truncation = truncation)
      u <- runif(1) # made a change here in while loop condition
      
      while (log(u)> -2*gam_param*sqrt(t)) {
        t <- rtgamma(1,shape=alpha,rate=1,truncation=truncation)
        u <- runif(1)
      }
    }
    
  }
  return(t)
}

#### Algorithm 2 of Liu et al 2013 ####
normal_rejection_sampler <- function(alpha,gam_param,truncation=NULL){
  if(alpha<1/2){
    stop("For normal RS, alpha needs to be greater than 1/2")
  }
  
  if(alpha==1/2){
    m <- max(-gam_param,0)
  }else{
    logm <- log(2*alpha-1)-log(gam_param+sqrt(gam_param^2+4*alpha-2))
    m <- exp(logm)
  }
  
  if(is.null(truncation)){
    x <- rtruncnorm(1,mean=m,sd=1/sqrt(2),a=0)
    u <- runif(1)
    
    while ((2*alpha-1)*log(m)+ log(u) >(2*alpha-1)*log(x)-2*(m+gam_param)*(x-m)) {
      x <- rtruncnorm(1,mean=m,sd=1/sqrt(2),a=0)
      u <- runif(1)
    }
  }else{
    x <- rtruncnorm(1,mean=m,sd=1/sqrt(2),a=0, b=sqrt(truncation))
    u <- runif(1)
    
    while ((2*alpha-1)*log(m)+ log(u) > (2*alpha-1)*log(x)-2*(m+gam_param)*(x-m)) {
      x <- rtruncnorm(1,mean=m,sd=1/sqrt(2),a=0, b=sqrt(truncation))
      u <- runif(1)
      #print(x)
    }
    
  }
  return(x^2)
}


# Algorithm 3 of Liu et al 2013 ####
gamma_rs_sqrt_scale <- function(alpha, gam_param,truncation=NULL){
  if(alpha<0){
    stop("For gamma RS on sqrt scale, alpha >0")
  }
  delta1 <- gam_param+sqrt(gam_param^2+4*alpha)
  r <- 2*alpha
  
  if(is.null(truncation)){
    x <- rgamma(1,r,delta1)
    u <- runif(1)
    
    while (log(u)>-(x-(delta1/2-gam_param))^2) {
      x <- rgamma(1,r,delta1)
      u <- runif(1)
    }
  }else{
    x <- rtgamma(1,shape=r,rate=delta1,truncation = sqrt(truncation))
    u <- runif(1)
    
    while (log(u)>-(x-(delta1/2-gam_param))^2) {
      x <- rtgamma(1,shape=r,rate=delta1,truncation = sqrt(truncation))
      u <- runif(1)
    }
    
  }
  return(x^2)
}

#### Optimal Rejection sampler for extended gamma distribution (Liu el al 2013) ####
ext_gamma_sampler <- function(alpha, gam_param,truncation=NULL){
  if(gam_param !=0){
    logC <- log(abs(gam_param)) - 0.5*log(alpha)
    C <- sign(gam_param)*exp(logC)
  }else if(gam_param==0){
    C <- 0
  }
  if(C<= -0.7){
    z <- normal_rejection_sampler(alpha,gam_param,truncation)
  }else if (-0.7 < C & C < 0.7){
    z <- gamma_rejection_sampler(alpha,gam_param,truncation)
  }else if (C >= 0.7){
    z <- gamma_rs_sqrt_scale(alpha,gam_param,truncation)
  }
  return(z)
}

#### main function ####
Blockg.lm <- function(x,y,
                      grp_idx=NULL,
                      adaptive=TRUE,
                      K=40, # Max number of mixture components 
                      burn=10000,
                      nmc=9000,
                      a_BNP=0, # hyperparameter for the nonparametric process (DP vs PY)
                               # a_BNP==0 implies fully Bayesian with a gamma(1,1) prior on a_BNP
                      a_a_BNP = 1, #hyperparameter for the nonparametric process (DP vs PY)
                      b_a_BNP = 1, #hyperparameter for the nonparametric process (DP vs PY)
                      thinning=10, 
                      model.prior="beta-binomial", # uniform, # decaying-beta-binomial 
                      model.init=NULL,
                      hyper.prior="Inv-gamma", # "hyper-g", "hyper-g-n",
                      # "beta-prime-MG","beta-prime"
                      tau2.fixed=FALSE,
                      tau2=1,
                      hyper.param=NULL,
                      DP.inference=NULL, # can be SB, Dir, condDir
                      prior.corr=TRUE,
                      model=NULL){ 
  
  n <- length(y)
  p <- ncol(x)
  
  if(prior.corr==TRUE & !is.null(model)){
    if(sum(model)>=n-1){
      stop("xtx inverse in g prior is not defined for p>n case. 
           Select model such that model size is <n-1.")
    }
  }
  
  if(adaptive==TRUE & is.null(DP.inference)){
    DP.inference="Dir"  
  }
  
  if(is.null(grp_idx)){
    if(adaptive==FALSE){
      stop("Either the argument grp_idx should be provided, or adaptive should be set to TRUE")
    }
    if(is.null(model)){
      grp_idx <- rep(1,p)
    }else{
      grp_idx <- rep(1,sum(model))
    }
    #Store useful quantites
    grp_size <- as.vector(table(grp_idx))
    grp_size_cs <- cumsum(grp_size)
    group_ids = unique(grp_idx)
    K0 = length(group_ids)
    
  }else if(!is.null(grp_idx)){
    #Store useful quantites
    grp_size <- as.vector(table(grp_idx))
    grp_size_cs <- cumsum(grp_size)
    group_ids = unique(grp_idx)
    K0 = length(group_ids)
    if(adaptive==FALSE){
      K=K0
    }
    if(length(grp_idx) != p){
      stop("The argument grp_idx must have length p, where p in the number of columns in X.")
    }
    
    if(any(diff(group_ids) > 1)) {
      stop("Groups skip a number somewhere in grp_idx. Ensure that grp_idx is an ordered sequence
         from 1 to p with no skips. A valid example is 1,1,1,2,2,3,3,3,4,5,5.")
    }
  }
  random <- F
  if(adaptive & a_BNP==0){
    a_BNP  <- rgamma(1,a_a_BNP,b_a_BNP)
    random <- T
  }
  
  
  #### Conditions/ tests on priors specified ####
  if(hyper.prior=="Inv-gamma"){
    if(is.null(hyper.param)){
      a1 <- 1/2
      a2 <- n/2
    }
    if(length(hyper.param)==2){
      if(hyper.param[1]>0 & hyper.param[2]>0){
        a1=hyper.param[1]
        a2=hyper.param[2]
      }else{
        stop("Inv-gamma requires a and b >0")
      }
    }
    if(length(hyper.param)>2| length(hyper.param)==1){
      stop("Inv-gamma specification requires only two 
           hyper-parameters which are both >0")
    }
  }
  
  if(hyper.prior=="hyper-g"){
    if(is.null(hyper.param)){a=3
    }else{
      if(length(hyper.param)>1| (hyper.param!=3 & hyper.param!=4)){
        stop("Hyper-g requires just one hyper parameter with recommended value 3 or 4")}
    }
    
  }
  if(hyper.prior=="hyper-g-n"){
    if(is.null(hyper.param)){
      a=3
    }else{
      if(length(hyper.param)>1| (hyper.param!=3 & hyper.param!=4)){
        stop("Hyper-g/n requires just one hyper 
                         parameter with value 3 or 4")}
      
    }
  }
  if(hyper.prior=="beta-prime-MG"){
    if(is.null(hyper.param)){
      a=-3/4
    }else{
      if(length(hyper.param)>1){
        stop("Maryuma and George recommended a to be between -1 and -1/2 and b to be adaptive")
      }
      if(!(-1< hyper.param & hyper.param< -1/2)){
        stop("Maryuma and George recommended a to be between -1 and -1/2")}
      
    }
  }
  if(hyper.prior=="beta-prime"){
    if(is.null(hyper.param)){
      a=-0.5
      b_param=-0.5
    }
    if(length(hyper.param)==2){
      if(hyper.param[1]>-1 & hyper.param[2]>-1){
        a=hyper.param[1]
        b_param=hyper.param[2]
      }else{
        stop("Beta-prime specification requires a and b >-1")
      }
    }
    if(length(hyper.param)>2| length(hyper.param)==1){
      stop("Beta-prime specification requires only two 
           hyper-parameters which are both >-1")
    }
  }
  
  #### Initialization ####
  # create matrix to save variables
  GammaSave = matrix(NA, nmc, p)
  BetaSave = matrix(NA, nmc, p+1)
  Sigma2Save <- matrix(NA, nmc, 1)
  Tau2Save <- matrix(NA, nmc, 1)
  logBF212Save <- matrix(NA,nmc,1)
  nclusterSave <- matrix(NA,nmc,1)
  logmargSave <- matrix(NA,nmc,1)
  gvalSave <- matrix(NA, nmc, p)
  grpidSave <- matrix(NA,nmc,p)
  timemat <- matrix(NA, nmc*thinning+burn, 7)
  xtx.full <- t(x)%*% x
  # Intialize parameters
  g.old <- n
  g_K <- rep(g.old,K)
  
  if(!is.null(model)){
    if(!is.null(model.init)& !all(model.init==model)){
      stop("model.init should be same as model or null when model is specified.")
    }
    gam <- model
    pgam <- sum(gam)
    b <- rep(0,pgam)
    
  }else{
    if(!is.null(model.init)){
      gam <- model.init
    }else{
      gam = rep(0,p)    
    }
    
    b <- rep(0, p)
  }
  
  g <- rep(g.old, p)#rinvgamma(p, 1/2, n/2)
  alpha <- mean(y)
  sigma2 <- 1
  tau2 <- tau2
  nu <- rinvgamma(1,1/2,1)
  # if DP.inference == "Dir"
  eta <- rbeta(1,1,1)
  # Update clust_prob (stick breaking probability using a beta distribution)
  #n_k <- count_subjects(K, grp_idx)
  n_k <- count_subjects(K, grp_idx[as.logical(gam)])
  
  
  if(adaptive==TRUE){
    if(DP.inference=="SB"){
      stick <- stick_break(K, n_k+1, a_BNP + sum(n_k)-cumsum(n_k),log = TRUE)
      lclust_prob <- stick$p
    }else if(DP.inference=="Dir"){
      lclust_prob <- log(rgamma(K,a_BNP/K+n_k,1))
      # if(sum(n_k)==0){
      #   #Use gamma representation
      #   lclust_gam_rep <- rgamma(K, a_BNP/K,1)
      #   lclust_prob <- log(lclust_gam_rep)-log(sum(lclust_gam_rep))
      # }else{
      #   lclust_prob <- log(rdirichlet(1,rep(a_BNP/K,K)+n_k))  
      # }
      
    }
  }
  
  
  #### MCMC Iteration loop ####
  for(t in 1:(nmc*thinning+burn)){
    
    if (t%%100 == 0){cat(paste(t," "))}
    
    #### Update Gamma####
    start_time <- Sys.time()
    if(is.null(model)){
    
      # Propose gamma
      gam.prop <- proposal.gamma(gam)
      
      if(sum(gam.prop)< n-1){
        logmarg.prop.obj <- log_marginal(x,y,g,gam.prop,hyper.prior=hyper.prior,
                                         prior.corr=prior.corr,tau2)
      }
      logmarg.curr.obj <- log_marginal(x,y,g, gam,hyper.prior=hyper.prior,
                                       prior.corr=prior.corr,tau2)
      # Calculate acceptance probability for (gam.prop,delta.cand)
      
      if(p==2){
        m2 <- c(1,1)
        m1 <- c(1,0)
        logmarg.m2.obj <- log_marginal(x,y,g,m2,hyper.prior=hyper.prior,
                                       prior.corr=prior.corr,tau2)
        logmarg.m1.obj <- log_marginal(x,y,g,m1,hyper.prior=hyper.prior,
                                       prior.corr=prior.corr,tau2)
        logbf21 <- logmarg.m2.obj$logmg - (logmarg.m1.obj$logmg)
      }else{
        logbf21 <- NA
      }
      
      
      # under beta-binomial
      if(model.prior=="beta-binomial"){
        if(sum(gam.prop)<n-1){
          oj.num.log <- -lchoose(p,sum(gam.prop)) + logmarg.prop.obj$logmg  
        }else{
          oj.num.log <- -Inf
        }
        oj.den.log <-  -lchoose(p,sum(gam))+logmarg.curr.obj$logmg
        
        # logbf21 <- logmarg.m2.obj$logmg - (logmarg.m1.obj$logmg)
      }else if (model.prior=="Uniform"){ # Under Uniform model prior
        # define oj.num.log and oj.den.log
        if(sum(gam.prop)<n-1){
          oj.num.log <- logmarg.prop.obj$logmg  
        }else{
          oj.num.log <- -Inf
        }
        
        oj.den.log <- logmarg.curr.obj$logmg
        # logbf21 <- logmarg.m2.obj$logmg - logmarg.m1.obj$logmg
      }else if(model.prior=="decaying-beta-binomial"){
          a.bb <- 1
          #s0 <- min(n,p)
          #k.bb <- (p-s0/2)/(log(p)*s0/2)
          if(n<=p){b.bb=1}else{
            b.bb <- log(p)#k.bb*log(p)  
          }
          
        # define oj.num.log and oj.den.log
        if(sum(gam.prop)<n-1){
          oj.num.log <- logmarg.prop.obj$logmg + lgamma(a.bb+sum(gam.prop))+lgamma(b.bb+p-sum(gam.prop))#dbbinom(sum(gam.prop), p, a.bb, b.bb,log = TRUE)  
        }else{
          oj.num.log <- -Inf
        }
        
        oj.den.log <- logmarg.curr.obj$logmg + lgamma(a.bb+sum(gam))+lgamma(b.bb+p-sum(gam))#dbbinom(sum(gam), p, a.bb, b.bb,log = TRUE) 
        
      }
      
      u.gam <- runif(1)
      
      #print(paste("Iteration",t,":", as.numeric(exp(oj.num.log-oj.den.log)),sep = ""))  
      
      
      #print(oj.den.log)
      loga.gam.prob <- min(as.numeric(oj.num.log-oj.den.log),0)
      if(log(u.gam)<=loga.gam.prob){
        gam <- gam.prop
        xtx <- logmarg.prop.obj$xtx
        xty <- logmarg.prop.obj$xty
        ggam <- logmarg.prop.obj$ggam
        sig2rate <- logmarg.prop.obj$sig2rate
        logmarg <- logmarg.prop.obj$logmg
      }else{
        gam <- gam
        xtx <- logmarg.curr.obj$xtx
        xty <- logmarg.curr.obj$xty
        ggam <- logmarg.curr.obj$ggam
        sig2rate <- logmarg.curr.obj$sig2rate
        logmarg <- logmarg.curr.obj$logmg
      }
    }else{
      logmarg.obj <- log_marginal(x,y,g,gam, hyper.prior=hyper.prior,
                                       prior.corr=prior.corr,tau2)
      gam <- gam
      xtx <- logmarg.obj$xtx
      xty <- logmarg.obj$xty
      ggam <- logmarg.obj$ggam
      sig2rate <- logmarg.obj$sig2rate
      logmarg <- logmarg.obj$logmg
      logbf21 <- NA
    }
    end_time <- Sys.time()
    timemat[t,1] <- end_time-start_time
    
    
    #### Update alpha and Beta #####
    start_time <- Sys.time()
    
    alpha <- rnorm(1, mean(y), sqrt(sigma2/n))
    pgam <- sum(gam)
    
    if(is.null(xtx)){
      b <- rep(0,p)
    }else{
      ggam_inv_half <- diag(1/sqrt(ggam),nrow = pgam,ncol = pgam) 
      #print(min(ggam))
      #print(max(ggam))
      if(prior.corr==TRUE){
        prec.mat <- (ggam_inv_half %*% xtx %*% ggam_inv_half)/tau2 + xtx  
      }else{
        prec.mat <- (diag(1/ggam,nrow = pgam,ncol = pgam))/tau2 + xtx
      }
      
      # covariance matrix is inverse of 1/sigma2*prec.mat and 
      # mean is cov matrix multiplied by xty/sigma^2 so that sigma2 cancel out in mean
      b <- custom4(1,1/sigma2*xty,1/sigma2*prec.mat)
      # cov.mat <- solve(prec.mat)
      # post.mean <- cov.mat%*% xty
      # b <- rmvnorm(1, post.mean, sigma2*cov.mat)
    }
    
    end_time <- Sys.time()
    timemat[t,2] <- end_time-start_time
    
    
    #### Update sigma2 ####
    start_time <- Sys.time()
    
    sigma2 <- rinvgamma(1, (n-1)/2, sig2rate/2)
    
    timemat[t,3] <- end_time-start_time
    
    
    #### Update grp_idx (1,..p) ####
    start_time <- Sys.time()
    if(adaptive==TRUE){
      # lclust_prob stores log of prior probability of being in that cluster
      # Update grp_idx and update K0 save updated grp_idx in grpidSave (later when saving iterations)
      grp_idx[gam==0] <- rcatlp(sum(gam==0),log_prob=lclust_prob) +1 #(indexing from 0)
      g <- g_K[grp_idx]
      var_in_mod <- which(gam==1)
      pgam <- length(var_in_mod)
      if(pgam!=0){
        #print(length(b))
        for (r in 1:pgam){
          ind.var <- var_in_mod[r]
          likl_cluster <- sapply(1:K, cluster_prop_llikelihood, b, xtx, g, gam, sigma2, g_K,r,prior.corr)
          post_lclust_prob <- lclust_prob + likl_cluster
          grp_idx[ind.var] <- rcatlp(1,log_prob = post_lclust_prob) +1 # indexing from 0
          g <- g_K[grp_idx]
        }
      }
      group_ids = unique(grp_idx)
      K0 = length(group_ids)
      K0_in_mod= length(unique(grp_idx[as.logical(gam)]))
      # Update clust_prob (stick breaking probability using a beta distribution)
      n_k <- count_subjects(K, grp_idx[as.logical(gam)])
      #n_k <- count_subjects(K, grp_idx)
      
      if(DP.inference=="SB"){
        stick <- stick_break(K, n_k+1, a_BNP + sum(n_k)-cumsum(n_k),log = TRUE)
        lclust_prob <- stick$p
      }else{
        lclust_prob <- log(rgamma(K, a_BNP/K+n_k,1))
        # if(sum(n_k)==0){
          #Use gamma representation
          #lclust_gam_rep <- rgamma(K, a_BNP/K,1)
          #lclust_prob <- log(lclust_gam_rep)-log(sum(lclust_gam_rep))
        # }else{
        #   lclust_prob <- log(rdirichlet(1,rep(a_BNP/K,K)+n_k))  
        #}
      }
      
      # Update a_BNP if random ==TRUE
      if(random==TRUE){
        if(DP.inference=="SB"){
          a_BNP <- sample_Plambda_posterior(1, stick$q, alpha0 = a_a_BNP,beta0 = b_a_BNP)
        }else if(DP.inference=="Dir"){
          # Use Escobar and West 1995 paper section 6
          if(pgam!=0){
            # Sample a_BNP
            z1 <- rcatlp(1, log_prob = c(log(a_a_BNP+K0_in_mod-1),log(pgam)+log(b_a_BNP-log(eta))))
            if(z1==0){
              a_BNP <- rgamma(1, a_a_BNP + K0_in_mod, b_a_BNP - log(eta))
            }else{
              a_BNP <- rgamma(1, a_a_BNP + K0_in_mod -1 , b_a_BNP - log(eta))
            }
            #Sample eta
            eta <- rbeta(1,a_BNP+1, pgam)
          }else{
            a_BNP <- rgamma(1,a_a_BNP,b_a_BNP)
          }
          # Sample a_BNP
          # z1 <- rcatlp(1, log_prob = c(log(a_a_BNP+K0-1),log(p)+log(b_a_BNP-log(eta))))
          # if(z1==0){
          #   a_BNP <- rgamma(1, a_a_BNP + K0, b_a_BNP - log(eta))
          # }else{
          #   a_BNP <- rgamma(1, a_a_BNP + K0 -1 , b_a_BNP - log(eta))
          # }
          #Sample eta
          #eta <- rbeta(1,a_BNP+1, p)
        }
          
      }
      
    }
    end_time <- Sys.time()
    timemat[t,4] <- end_time-start_time
    
    
    
    #### Update g ####
    start_time <- Sys.time()
    pgam <- sum(gam)
    
    if(is.null(xtx)){
      C <- NULL
    }else{
      bvec <- as.vector(b)
      bvec.full <- rep(0,p)
      bvec.full[which(gam==1)] <- bvec
      if(prior.corr==TRUE){
        C <- (2*sigma2*tau2)^{-1}* diag(bvec.full,nrow=length(bvec.full),ncol = 
                                     length(bvec.full)) %*% xtx.full %*% 
          diag(bvec.full, nrow=length(bvec.full),ncol = length(bvec.full))
        
      }else{
        C <- (2*sigma2*tau2)^{-1}* diag(bvec.full^2,nrow=length(bvec.full),ncol = 
                                     length(bvec.full))
      }
    }

    for(k in 1:K){
      grp_mem <- which(grp_idx==k)
      grp_mem_in_mod <- which(grp_idx==k & gam==1)
      s_k <- length(grp_mem_in_mod)
      if(s_k!=0){
        p_k <- length(grp_mem_in_mod)
        #print(pgam)
        #print((grp_mem_in_mod))
        #print((C))
        
        if(pgam==p_k){
            c_k <- sum(C)
            d_k <- 0
        }else{
          c_k <- sum(C[grp_mem_in_mod,grp_mem_in_mod])
          d_k <- sum(2*C[grp_mem_in_mod,-grp_mem_in_mod]%*% 
                       diag(1/sqrt(g[-grp_mem_in_mod]),nrow = 
                              p-length(grp_mem_in_mod)))
        }
        
        # sample g_k from that distribution using slice + rejection sampling
        if(hyper.prior=="Inv-gamma"){
          # draw from an extended Gamma distribution
          gam_prime <- d_k/(2*sqrt(c_k+a2))
          gk_inv <- ext_gamma_sampler(alpha = a1+p_k/2, gam_param = 
                                       gam_prime,truncation = NULL)
          gk_inv <- gk_inv/(c_k+a2)
          g_K[k] <- 1/gk_inv
          g[grp_mem] <- 1/gk_inv
        }else if(hyper.prior=="hyper-g"){
          t_i <- 1/g_K[k] # Think about it carefully g or g_gam
          #print(t_i)
          # Slice sampling approach
          ht_i <- (1+t_i)^{-a/2}
          u_i <- runif(1,0,ht_i)
          truncation <- c_k*(u_i^{-2/a}-1)
          zeta <- d_k/(2*sqrt(c_k))
          #print(d_k)
          #print(c_k)
          #print(zeta)
          z_i <- ext_gamma_sampler(alpha = (a+p_k-2)/2,gam_param = zeta,
                                   truncation = truncation)
          gk_inv <- z_i/c_k
          g_K[k] <- 1/gk_inv
          g[grp_mem] <- 1/gk_inv
          
        }else if(hyper.prior=="hyper-g-n"){
          t_i <- 1/g_K[k] 
          # Slice sampling approach
          ht_i <- (1+n*t_i)^{-a/2}
          u_i <- runif(1,0,ht_i)
          truncation <- c_k*1/n*(u_i^{-2/a}-1)
          zeta <- d_k/(2*sqrt(c_k))
          z_i <- ext_gamma_sampler(alpha = (a+p_k-2)/2,gam_param = zeta,
                                   truncation = truncation)
          gk_inv <- z_i/c_k
          g_K[k] <- 1/gk_inv
          g[grp_mem] <- 1/gk_inv
        }else if(hyper.prior=="beta-prime"|hyper.prior=="beta-prime-MG"){
          t_i <- 1/g_K[k] 
          
          # Slice sampling approach
          pgam <- sum(gam)
          if(hyper.prior=="beta-prime-MG"){
            b_param <- (n-pgam-5)/2 -a
          }else if(hyper.prior=="beta-prime"){
            b_param <- b_param
          }
          #print(paste("Cii:",C[count,count]))
          #print(paste("di:",d_i))
          if(c_k==0 & d_k==0){
            bp.tran <- rbeta(1,a+p_k/2+1,b_param+1-p_k/2)
            g[ind] <- exp(log(bp.tran)-log(1-bp.tran))
          }else{
            ht_i <- (1+t_i)^{-(a+b_param+2)}#{-(n-pgam-1)/2}
            u_i <- runif(1,0,ht_i)
            truncation <- c_k*(u_i^{-1/(a+b_param+2)}-1)#(u_i^{-2/(n-pgam-1)}-1)
            zeta <- d_k/(2*sqrt(c_k))
            # if(abs(zeta)>10^5 | is.nan(zeta)){
            #   print(pgam)
            #   print(count)
            #   print(paste("g_i:",ggam[count]))
            #   print(paste("b_i:",bvec[count]))
            #   print(paste("xtxii:",xtx[count,count]))
            #   print(paste("Cii:",C[count,count]))
            #   print(paste("di:", d_i))
            # }
            z_i <- ext_gamma_sampler(alpha = a+p_k/2+1,gam_param = zeta,
                                     truncation = truncation)
            gk_inv <- z_i/c_k
            g_K[k] <- 1/gk_inv
            g[grp_mem] <- 1/gk_inv
          }
      }}else{
        # sample g_k from prior distribution
        if(hyper.prior=="Inv-gamma"){
          g_K[k] <- rinvgamma(1,a1,a2) 
        }else if(hyper.prior=="hyper-g"){
          g_K[k] <- rhyperg(1,a)
        }else if(hyper.prior=="hyper-g-n"){
          g_K[k] <- rhypergn(1,a,n)
        }else if(hyper.prior=="beta-prime"|hyper.prior=="beta-prime-MG"){
          if(hyper.prior=="beta-prime"){
            b_param <- b_param
          }else if(hyper.prior=="beta-prime-MG"){
            b_param <- (n-pgam-5)/2 -a
          }
          bp.tran <- rbeta(1,a+1,b_param+1)
          g_K[k] <- exp(log(bp.tran)-log(1-bp.tran))#rbetapr(1, a+1, b_param+1)
        }
        if(length(grp_mem)!=0){
          g[grp_mem] <- g_K[k]
        }
      }
    }
    
    end_time <- Sys.time()
    timemat[t,5] <- end_time-start_time

    if(tau2.fixed==FALSE){
      start_time <- Sys.time()
      #### Update tau2 and nu ####
      if(pgam>0){
        ggam <- g[as.logical(gam)]
        ggam_inv_half <- diag(1/sqrt(ggam),nrow = pgam,ncol = pgam) 
        if(prior.corr==TRUE){
          tau2rate <- (t(b)%*%(ggam_inv_half %*% xtx %*% ggam_inv_half)%*% b)/(2*sigma2)  
        }else{
          tau2rate <- (t(b)%*%(diag(1/ggam,nrow = pgam,ncol = pgam))%*% b)/(2*sigma2)
        }
        #print(tau2)
        tau2 <- 1/rgamma(1, (pgam+1)/2, 1/nu+ tau2rate)
      }else{
        tau2 <- 1/rgamma(1, 1/2,1/nu)
      }
      end_time <- Sys.time()
      timemat[t,6] <- end_time-start_time
      
      start_time <- Sys.time()
      
      nu <- 1/rgamma(1, 1, 1+1/tau2)
      
      end_time <- Sys.time()
      timemat[t,7] <- end_time-start_time
      
    }
    
    
    #### Store results as a list ####
    betastore=rep(0,p)
    #Save results post burn-in
    if(t > burn && (t - burn) %% thinning == 0){
      rr  <- floor((t - burn) / thinning)
      GammaSave[rr, ] = gam
      # count3=1
      # gam.withintercept <- c(1,gam)
      # betastore[1] <- alpha
      # for (k in 2:(p+1)){
      #   if(gam.withintercept[k]==1){
      #     betastore[k]= b[count3]
      #     count3=count3+1
      #   }
      # }
      betastore[which(gam==1)] <- b
      betastore <- c(alpha,betastore)
      BetaSave[rr, ] = betastore
      Sigma2Save[rr, ] <- sigma2
      Tau2Save[rr, ] <- tau2
      if(adaptive){
        nclusterSave[rr, ] <- K0_in_mod
      }else{
        nclusterSave[rr, ] <- K0
      }
      logmargSave[rr, ] <- logmarg
      gvalSave[rr, ] <- g
      grpidSave[rr, ] <- grp_idx
      logBF212Save[rr, ] <- logbf21
    }
  }
  
  result <- list("BetaSamples"=BetaSave,
                 "GammaSamples"=GammaSave,
                 "Sigma2Samples"=Sigma2Save,
                 "Tau2Samples"=Tau2Save,
                 "ncluster"=nclusterSave,
                 "grpid"=grpidSave,
                 "gsamples"=gvalSave,
                 "logBF21"=logBF212Save,
                 "timemat"=timemat)
  # Return object
  return(result)
  
}



